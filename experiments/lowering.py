"""Run the proved lowering, then compile its emitted C or CUDA artifact.

The source-to-IR theorem is checked in Lean. The IR printer, native compilers,
FFI, and hardware remain trusted. This module contains no kernel implementation.
"""

import argparse
import ctypes
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

from experiments.gather import (GatherCase, ROOT, SIZE_MAX,
                                UINT32_MAX, UINT64_MAX, cases, reference)


EXECUTABLE = ROOT / ".lake/build/bin/keystone_lower"


def request_for(case) -> dict:
    return {"page_size": case.page_size, "tokens": case.tokens,
            "lanes": case.launched_threads, "table": list(case.table), "cache": list(case.cache)}


def lower(request: dict) -> dict:
    process = subprocess.run([str(EXECUTABLE)], input=json.dumps(request),
                             capture_output=True, text=True, timeout=30)
    response = json.loads(process.stdout)
    if process.returncode or response.get("status") != "ok":
        raise ValueError(f"lowering request failed: {response}")
    return response


class BackendUnavailable(RuntimeError):
    """An optional compiler/device is absent; execution failures are different."""


class LoweredNative:
    def __init__(self, response: dict, cuda: bool = False,
                 directory: Path = ROOT / "artifacts/native") -> None:
        self.cuda = cuda
        if cuda and (response.get("program") != "gather" or not response.get("gather_contract")):
            raise ValueError("CUDA runner requires the gather kernel with a valid memory contract")
        compiler = shutil.which("nvcc" if cuda else "cc")
        if compiler is None:
            raise BackendUnavailable("nvcc is unavailable" if cuda else "cc is unavailable")
        source = response["cuda_source" if cuda else "c_source"]
        version = subprocess.run([compiler, "--version"], capture_output=True,
                                 text=True, check=True).stdout.strip()
        flags = (["-O2", "-std=c++11", "-shared", "-Xcompiler=-fPIC"] if cuda
                 else ["-O2", "-std=c11", "-shared", "-fPIC"])
        key = hashlib.sha256(json.dumps([source, compiler, version, flags]).encode()).hexdigest()
        directory = Path(directory)
        directory.mkdir(parents=True, exist_ok=True)
        source_path = directory / (key + (".cu" if cuda else ".c"))
        library_path = directory / (key + ".so")
        if not library_path.exists() or not source_path.exists() or source_path.read_text() != source:
            with tempfile.TemporaryDirectory(dir=directory) as temporary:
                temporary = Path(temporary)
                staged_source = temporary / source_path.name
                staged_source.write_text(source)
                subprocess.run([compiler, *flags, str(staged_source), "-o", str(temporary / library_path.name)],
                               capture_output=True, text=True, check=True, timeout=60)
                staged_source.replace(source_path)
                (temporary / library_path.name).replace(library_path)
        self.library = ctypes.CDLL(str(library_path.resolve()))
        self.kernel = self.library.lowered_kernel
        self.kernel.argtypes = [ctypes.POINTER(ctypes.c_uint32), ctypes.c_uint64,
                               ctypes.POINTER(ctypes.c_uint64), ctypes.c_uint64,
                               ctypes.POINTER(ctypes.c_uint32)] + [ctypes.c_uint64] * 4
        self.kernel.restype = ctypes.c_int
        self.metadata = {"backend": "cuda" if cuda else "cpu-c", "compiler": compiler,
                         "source": str(source_path)}
        if cuda:
            count = ctypes.c_int()
            self.library.available_devices.argtypes = [ctypes.POINTER(ctypes.c_int)]
            self.library.available_devices.restype = ctypes.c_int
            status = self.library.available_devices(ctypes.byref(count))
            if status or count.value == 0:
                raise BackendUnavailable(f"CUDA device unavailable (status={status}, count={count.value})")

    def run(self, request: dict) -> list[int]:
        def bounded(value, maximum):
            if type(value) is not int or not 0 <= value <= maximum:
                raise ValueError("native launch contains an invalid integer")
            return value

        cache = tuple(bounded(v, UINT32_MAX) for v in request["cache"])
        table = tuple(bounded(v, UINT64_MAX) for v in request["table"])
        if len(cache) > SIZE_MAX // 4 or len(table) > SIZE_MAX // 8:
            raise ValueError("native allocation exceeds addressable memory")
        n = bounded(request["tokens"], min(UINT64_MAX, SIZE_MAX // 4))
        b = bounded(request["page_size"], UINT64_MAX)
        lanes = bounded(request["lanes"], UINT64_MAX)
        if self.cuda:
            # The generic theorem is per lane. Restrict parallel native launches
            # to the proved gather specialization: successful, disjoint writes.
            if "source" in request or lanes < n:
                raise ValueError("CUDA runner accepts only complete gather launches")
            GatherCase(b, n, 1, table, cache)
        cache_buffer = (ctypes.c_uint32 * len(cache))(*cache)
        table_buffer = (ctypes.c_uint64 * len(table))(*table)
        output = (ctypes.c_uint32 * n)()
        status = self.kernel(cache_buffer, len(cache), table_buffer, len(table), output,
                             n, b, n, lanes)
        if status:
            raise RuntimeError(f"lowered native program rejected execution (status={status})")
        return list(output)


class NativeGather:
    """Specialize the native runner to the Lean-lowered gather."""
    cuda = False

    def __init__(self, build_dir: Path = ROOT / "artifacts/native") -> None:
        program = lower(request_for(GatherCase(1, 0, 1, (), ())))
        self._native = LoweredNative(program, cuda=self.cuda, directory=build_dir)

    def run(self, case: GatherCase) -> list[int]:
        if not isinstance(case, GatherCase):
            raise TypeError("native execution requires a validated GatherCase")
        return self._native.run(request_for(case))


class CudaGather(NativeGather):
    cuda = True


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cuda", action="store_true", help="require real CUDA execution")
    parser.add_argument("--source", action="store_true", help="print emitted C/CUDA without compiling")
    parser.add_argument("--output", type=Path, help="write detailed execution traces")
    args = parser.parse_args()
    if args.source:
        result = lower(request_for(next(cases(count=0))))
        print(result["cuda_source" if args.cuda else "c_source"], end="")
        return
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.unlink(missing_ok=True)
    records, native = [], None
    for case in cases(count=0):
        request = request_for(case)
        result = lower(request)
        if native is None:
            native = LoweredNative(result, cuda=args.cuda)
        actual = native.run(request)
        expected = reference(case)
        if (not result["observable_equivalent"] or result["source"]["status"] != "ok" or
                result["target"]["status"] != "ok" or
                actual != result["target"]["output"] or actual != expected):
            raise AssertionError(f"lowering disagreement: {request} -> {result}")
        records.append({"request": request, "source": result["source"], "target": result["target"],
                        "native": actual, "reference": expected})
    if args.output:
        args.output.write_text(json.dumps({"backend": native.metadata,
            "instructions": result["instructions"], "cases": records}, indent=2) + "\n")
    print(f"Lowering: {len(result['instructions'])} target instructions; "
          f"{len(records)} source/target/native/reference cases agree ({native.metadata['backend']}).")


if __name__ == "__main__":
    main()
