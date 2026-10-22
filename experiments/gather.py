"""KV-gather launches, an independent specification, and the Lean interpreter adapter."""

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
    """A validated launch contract with immutable, privately copied buffers.

    Pages are complete and may be shared or permuted. Output is always a fresh
    allocation. Every page-table entry names an allocated page, including unused
    entries: this is slightly stronger than the kernel's minimum precondition.
    """

    page_size: int
    num_tokens: int
    block_size: int
    page_table: tuple[int, ...]
    kv_cache: tuple[int, ...]

    def __post_init__(self) -> None:
        _integer("page_size", self.page_size, UINT64_MAX, 1)
        _integer("num_tokens", self.num_tokens, min(UINT64_MAX, SIZE_MAX // 4))
        _integer("block_size", self.block_size, 1024, 1)
        object.__setattr__(self, "page_table", tuple(self.page_table))
        object.__setattr__(self, "kv_cache", tuple(self.kv_cache))
        if len(self.kv_cache) % self.page_size:
            raise ValueError("kv_cache must contain complete physical pages")
        if len(self.kv_cache) > min(UINT64_MAX, SIZE_MAX // 4):
            raise ValueError("kv_cache allocation exceeds native addressing limits")
        if len(self.page_table) > SIZE_MAX // 8:
            raise ValueError("page table exceeds native addressing limits")
        required_pages = (self.num_tokens + self.page_size - 1) // self.page_size
        if len(self.page_table) < required_pages:
            raise ValueError("page table does not cover all tokens")
        for page in self.page_table:
            _integer("physical page", page, UINT64_MAX)
            if page >= len(self.kv_cache) // self.page_size:
                raise ValueError("page table references an unallocated physical page")
        for entry in self.kv_cache:
            _integer("KV-cache entry", entry, UINT32_MAX)
        if self.num_threads > UINT64_MAX:
            raise ValueError("rounded launch size overflows uint64")

    @property
    def num_threads(self) -> int:
        """Threads launched: num_tokens rounded up to whole blocks."""
        return ((self.num_tokens + self.block_size - 1) // self.block_size) * self.block_size

    def request(self, schedule=None) -> dict:
        result = {"page_size": self.page_size, "num_tokens": self.num_tokens,
                  "block_size": self.block_size, "page_table": list(self.page_table),
                  "kv_cache": list(self.kv_cache)}
        if schedule is not None:
            result["schedule"] = list(schedule)
        return result


def expected_output(case: GatherCase) -> list[int]:
    """Independent specification: concatenate the request's pages in order, then trim."""
    required = (case.num_tokens + case.page_size - 1) // case.page_size
    pages = (case.kv_cache[p * case.page_size:(p + 1) * case.page_size]
             for p in case.page_table[:required])
    return [entry for page in pages for entry in page][:case.num_tokens]


class LeanGather:
    def __init__(self, executable: Path = ROOT / ".lake/build/bin/keystone_gpu") -> None:
        self.executable = Path(executable).resolve()

    def run(self, case: GatherCase, schedule=None) -> dict:
        response = subprocess.run([str(self.executable)], input=json.dumps(case.request(schedule)),
                                  capture_output=True, text=True, check=True, timeout=30)
        result = json.loads(response.stdout)
        if not isinstance(result, dict):
            raise ValueError("Lean interpreter returned a non-object response")
        return result


def cases(seed: int = 2026, count: int = 0):
    """Deterministic tail tiles, sharing, permutations, and all uint32 entries."""
    yield GatherCase(4, 5, 4, (2, 0), tuple(range(12)))
    yield GatherCase(2, 4, 8, (1, 1), (0, UINT32_MAX, 0x80000000, 0x7FC00000))
    yield GatherCase(4, 0, 32, (), ())
    rng = random.Random(seed)
    for _ in range(count):
        page_size = rng.choice((1, 2, 3, 4, 7, 16))
        pages = rng.randrange(1, 10)
        num_tokens = rng.randrange(0, 10 * page_size + 1)
        page_table = tuple(rng.randrange(pages)
                           for _ in range((num_tokens + page_size - 1) // page_size))
        kv_cache = tuple(rng.getrandbits(32) for _ in range(pages * page_size))
        yield GatherCase(page_size, num_tokens, rng.choice((1, 4, 8, 32)), page_table, kv_cache)
