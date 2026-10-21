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
    """A delayed operation captures an ordered page table, not a cache copy."""

    ticket: int
    table: tuple[int, ...]
    tokens: int

    @classmethod
    def from_ticket(cls, ticket: dict, tokens: int):
        return cls(ticket["id"], tuple(lease["page"] for lease in ticket["pages"]), tokens)

    def input_now(self, controller: Controller, cache: list[int],
                  page_size: int, block_size: int = 8) -> GatherCase:
        state = controller.state
        ticket = next((t for t in state["pending"] if t["id"] == self.ticket), None)
        if ticket is None or self.table != tuple(p["page"] for p in ticket["pages"]):
            raise ValueError("gather does not match a live operation's captured page table")
        if any(p not in state["allocations"] for p in ticket["pages"]):
            raise ValueError("captured lease is no longer allocated")
        if len(cache) != state["capacity"] * page_size:
            raise ValueError("physical buffer does not match controller capacity")
        return GatherCase(page_size, self.tokens, block_size, self.table, tuple(cache))
