"""Controller lifetimes and the runtime's live-ticket boundary."""
from dataclasses import replace
import unittest

from experiments.gather import reference
from experiments.runtime import Controller, PendingGather


class KVTests(unittest.TestCase):
    def launch(self):
        controller = Controller(2)
        a = controller.command("allocate", owner=10)["lease"]
        b = controller.command("allocate", owner=10)["lease"]
        ticket = controller.command("submit", owner=10, pages=[b, a])["ticket"]
        return controller, ticket, PendingGather.from_ticket(ticket, tokens=3)

    def test_reverse_completion_and_stale_events(self):
        controller = Controller(1)
        a = controller.command("allocate", owner=10)["lease"]
        first = controller.command("submit", owner=10, pages=[a])["ticket"]
        second = controller.command("submit", owner=10, pages=[a])["ticket"]
        controller.command("retire", owner=10)
        controller.command("complete", ticket=second["id"])
        self.assertEqual(controller.state["allocations"], [a])
        self.assertFalse(controller.command("allocate", owner=20)["accepted"])
        controller.command("complete", ticket=first["id"])
        b = controller.command("allocate", owner=20)["lease"]
        self.assertEqual(a["page"], b["page"])
        self.assertNotEqual(a["generation"], b["generation"])
        controller.command("submit", owner=20, pages=[b])
        before = controller.state
        self.assertFalse(controller.command("complete", ticket=first["id"])["accepted"])
        self.assertEqual(controller.state, before)
        self.assertFalse(controller.command("allocate", owner=10)["accepted"])
        self.assertFalse(controller.command("submit", owner=20, pages=[a])["accepted"])

    def test_multi_page_order_ownership_and_partial_reclamation(self):
        controller, ticket, _ = self.launch()
        b, a = ticket["pages"]
        self.assertEqual([p["page"] for p in ticket["pages"]], [1, 0])
        self.assertFalse(controller.command("submit", owner=20, pages=[a])["accepted"])
        second = controller.command("submit", owner=10, pages=[b, b])["ticket"]
        controller.command("retire", owner=10)
        controller.command("complete", ticket=ticket["id"])
        self.assertEqual(controller.state["allocations"], [b])
        controller.command("complete", ticket=second["id"])
        self.assertEqual(controller.state["allocations"], [])

    def test_pending_launch_reads_current_cache(self):
        controller, _, job = self.launch()
        cache = [10, 11, 20, 21]
        before = job.input_now(controller, cache, 2)
        controller.command("retire", owner=10)
        cache[2] = 99
        self.assertEqual(reference(before), [20, 21, 10])
        self.assertEqual(reference(job.input_now(controller, cache, 2)), [99, 21, 10])

    def test_adapter_rejects_forged_and_completed_jobs(self):
        controller, ticket, job = self.launch()
        for forged in [replace(job, ticket=999), replace(job, table=(0, 1))]:
            with self.assertRaises(ValueError):
                forged.input_now(controller, [10, 11, 20, 21], 2)
        with self.assertRaises(ValueError):
            job.input_now(controller, [10, 11, 20, 21, 30, 31], 2)
        controller.command("complete", ticket=ticket["id"])
        with self.assertRaises(ValueError):
            job.input_now(controller, [10, 11, 20, 21], 2)

    def test_empty_pool_and_empty_operation(self):
        controller = Controller(0)
        self.assertFalse(controller.command("allocate", owner=1)["accepted"])
        ticket = controller.command("submit", owner=1, pages=[])["ticket"]
        controller.command("retire", owner=1)
        controller.command("complete", ticket=ticket["id"])
        self.assertEqual(controller.state["pending"], [])
