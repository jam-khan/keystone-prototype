"""Gather inputs, independent specification, and the Lean interpreter adapter."""

from __future__ import annotations

import ctypes
from dataclasses import dataclass
import json
from pathlib import Path
import random
import subprocess


ROOT = Path(__file__).resolve().parents[1]
UINT32_MAX = (1 << 32) - 1
UINT64_MAX = (1 << 64) - 1
SIZE_MAX = ctypes.c_size_t(-1).value


def _integer(name: str, value: int, maximum: int, minimum: int = 0) -> None:
    if type(value) is not int or not minimum <= value <= maximum:
        raise ValueError(f"{name} must be an integer in [{minimum}, {maximum}]")


@dataclass(frozen=True)
class GatherCase:
    """A validated launch contract with immutable, privately copied inputs.

    Pages are complete and may be shared or permuted. Output is always a fresh
    allocation. Every table entry names an allocated page, including unused
    entries: this is slightly stronger than the kernel's minimum precondition.
    """

    page_size: int
    tokens: int
    block_size: int
    table: tuple[int, ...]
    cache: tuple[int, ...]

    def __post_init__(self) -> None:
        _integer("page_size", self.page_size, UINT64_MAX, 1)
        _integer("tokens", self.tokens, min(UINT64_MAX, SIZE_MAX // 4))
        _integer("block_size", self.block_size, 1024, 1)
        object.__setattr__(self, "table", tuple(self.table))
        object.__setattr__(self, "cache", tuple(self.cache))
        if len(self.cache) % self.page_size:
            raise ValueError("cache must contain complete physical pages")
        if len(self.cache) > min(UINT64_MAX, SIZE_MAX // 4):
            raise ValueError("cache allocation exceeds native addressing limits")
        if len(self.table) > SIZE_MAX // 8:
            raise ValueError("page table exceeds native addressing limits")
        required_pages = (self.tokens + self.page_size - 1) // self.page_size
        if len(self.table) < required_pages:
            raise ValueError("page table does not cover all logical tokens")
        for page in self.table:
            _integer("physical page", page, UINT64_MAX)
            if page >= len(self.cache) // self.page_size:
                raise ValueError("page table references an unallocated physical page")
        for value in self.cache:
            _integer("cache payload", value, UINT32_MAX)
        if self.launched_threads > UINT64_MAX:
            raise ValueError("rounded launch size overflows uint64")

    @property
    def launched_threads(self) -> int:
        return ((self.tokens + self.block_size - 1) // self.block_size) * self.block_size

    def request(self, schedule=None, mutation: str = "none") -> dict:
        result = {"page_size": self.page_size, "tokens": self.tokens,
                  "block_size": self.block_size, "table": list(self.table),
                  "cache": list(self.cache), "mutation": mutation}
        if schedule is not None:
            result["schedule"] = list(schedule)
        return result


def reference(case: GatherCase) -> list[int]:
    """Independent logical specification: concatenate selected pages, then trim."""
    required = (case.tokens + case.page_size - 1) // case.page_size
    pages = (case.cache[p * case.page_size:(p + 1) * case.page_size]
             for p in case.table[:required])
    return [word for page in pages for word in page][:case.tokens]


class LeanGather:
    def __init__(self, executable: Path = ROOT / ".lake/build/bin/keystone_gpu") -> None:
        self.executable = Path(executable).resolve()

    def run(self, case: GatherCase, schedule=None, mutation: str = "none") -> dict:
        response = subprocess.run([str(self.executable)], input=json.dumps(case.request(schedule, mutation)),
                                  capture_output=True, text=True, check=True, timeout=30)
        result = json.loads(response.stdout)
        if not isinstance(result, dict):
            raise ValueError("Lean interpreter returned a non-object response")
        return result


def cases(seed: int = 2026, count: int = 0):
    """Deterministic tail tiles, sharing, permutations, and all uint32 payloads."""
    yield GatherCase(4, 5, 4, (2, 0), tuple(range(12)))
    yield GatherCase(2, 4, 8, (1, 1), (0, UINT32_MAX, 0x80000000, 0x7FC00000))
    yield GatherCase(4, 0, 32, (), ())
    rng = random.Random(seed)
    for _ in range(count):
        page_size = rng.choice((1, 2, 3, 4, 7, 16))
        pages = rng.randrange(1, 10)
        tokens = rng.randrange(0, 10 * page_size + 1)
        table = tuple(rng.randrange(pages) for _ in range((tokens + page_size - 1) // page_size))
        cache = tuple(rng.getrandbits(32) for _ in range(pages * page_size))
        yield GatherCase(page_size, tokens, rng.choice((1, 4, 8, 32)), table, cache)


def mutation_cases() -> dict[str, GatherCase]:
    """Faults are interpreted in Lean, never executed as unsafe native code.

    The wrong-page example stays in bounds but computes the wrong values;
    memory safety alone therefore cannot establish functional correctness.
    """
    return {"missing_mask": GatherCase(4, 5, 4, (2, 0), tuple(range(12))),
            "wrong_page": GatherCase(2, 4, 4, (1, 0), (10, 11, 20, 21))}

