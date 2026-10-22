"""Replay commands through Lean; delayed gathers capture pages, not their contents."""

from dataclasses import dataclass
import json
from pathlib import Path
import subprocess

from experiments.gather import GatherCase, ROOT


class Controller:
    def __init__(self, capacity: int,
                 executable: Path = ROOT / ".lake/build/bin/keystone_kv") -> None:
        self.capacity = capacity
        self.executable = Path(executable).resolve()
        self.actions = []
        self.response = self._replay([])

    def _replay(self, actions: list) -> dict:
        process = subprocess.run(
            [str(self.executable)], input=json.dumps({"capacity": self.capacity, "actions": actions}),
            capture_output=True, text=True, timeout=30)
        response = json.loads(process.stdout)
        if process.returncode or response.get("status") != "ok":
            raise ValueError(f"controller rejected request: {response}")
        return response

    @property
    def state(self) -> dict:
        return self.response["state"]

    def command(self, op: str, **fields) -> dict:
        # JSON roundtrip prevents later caller mutation from changing history.
        action = json.loads(json.dumps({"op": op, **fields}))
        response = self._replay(self.actions + [action])
        self.actions.append(action)
        self.response = response
        return response["trace"][-1]["result"]


@dataclass(frozen=True)
class PendingGather:
    """A delayed operation captures an ordered page table, not a KV-cache copy."""

    ticket: int
    page_table: tuple[int, ...]
    num_tokens: int

    @classmethod
    def from_ticket(cls, ticket: dict, num_tokens: int):
        return cls(ticket["id"], tuple(lease["page"] for lease in ticket["pages"]), num_tokens)

    def case_now(self, controller: Controller, kv_cache: list[int],
                 page_size: int, block_size: int = 8) -> GatherCase:
        """The launch this job would run now, against the current KV-cache contents."""
        state = controller.state
        ticket = next((t for t in state["pending"] if t["id"] == self.ticket), None)
        if ticket is None or self.page_table != tuple(p["page"] for p in ticket["pages"]):
            raise ValueError("gather does not match a live operation's captured page table")
        if any(p not in state["allocations"] for p in ticket["pages"]):
            raise ValueError("captured lease is no longer allocated")
        if len(kv_cache) != state["capacity"] * page_size:
            raise ValueError("KV cache does not match controller capacity")
        return GatherCase(page_size, self.num_tokens, block_size, self.page_table, tuple(kv_cache))
