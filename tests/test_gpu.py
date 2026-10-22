"""GPU model, schedules, and native gather agree on the same inputs."""
from pathlib import Path
import random
import tempfile
import unittest

from experiments.gather import GatherCase, LeanGather, cases, expected_output
from experiments.lowering import NativeGather


class GPUTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.native = NativeGather(Path(cls.directory.name))
        cls.lean = LeanGather()

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def test_model_native_and_specification(self):
        for case in cases(seed=2026, count=12):
            result = self.lean.run(case)
            self.assertEqual(result["status"], "completed")
            self.assertEqual(result["output"], expected_output(case))
            self.assertEqual(self.native.run(case), expected_output(case))

    def test_interleavings_preserve_entries_and_write_ownership(self):
        case = GatherCase(3, 7, 4, (2, 0, 2), tuple(range(9)))
        threads = list(range(case.num_threads))
        shuffled = threads * 6
        random.Random(2718).shuffle(shuffled)
        for schedule in [shuffled, list(reversed(threads)) * 6,
                         [tid for tid in threads for _ in range(6)]]:
            result = self.lean.run(case, schedule=schedule)
            self.assertEqual(result["status"], "completed")
            self.assertEqual(result["output"], expected_output(case))
            self.assertTrue(all(a["thread"] < case.num_tokens for a in result["accesses"]))
            stores = [a for a in result["accesses"] if a["buffer"] == "output"]
            self.assertEqual(sorted(a["index"] for a in stores), list(range(case.num_tokens)))
            self.assertTrue(all(a["index"] == a["thread"] for a in stores))

    def test_starvation_and_invalid_thread(self):
        case = GatherCase(2, 3, 4, (0, 1), (10, 11, 20, 21))
        result = self.lean.run(case, schedule=[0] * 30)
        self.assertEqual(result["status"], "incomplete")
        self.assertEqual(result["output"], [10, None, None])
        self.assertEqual(self.lean.run(case, schedule=[4])["fault"],
                         {"kind": "invalid_thread", "thread": 4})

    def test_native_launch_contract(self):
        base = dict(page_size=2, num_tokens=3, block_size=4, page_table=(0, 1),
                    kv_cache=(10, 11, 20, 21))
        for change in [dict(page_size=0), dict(num_tokens=True), dict(num_tokens=5),
                       dict(page_table=(0, 2)), dict(kv_cache=(1 << 32,) * 4)]:
            with self.subTest(change=change), self.assertRaises(ValueError):
                GatherCase(**dict(base, **change))
