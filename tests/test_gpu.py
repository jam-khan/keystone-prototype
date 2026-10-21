"""GPU model, schedules, and native gather agree on the same inputs."""
from pathlib import Path
import random
import tempfile
import unittest

from experiments.gather import GatherCase, LeanGather, cases, mutation_cases, reference
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
            self.assertEqual(result["output"], reference(case))
            self.assertEqual(self.native.run(case), reference(case))

    def test_interleavings_preserve_values_and_write_ownership(self):
        case = GatherCase(3, 7, 4, (2, 0, 2), tuple(range(9)))
        lanes = list(range(case.launched_threads))
        shuffled = lanes * 6
        random.Random(2718).shuffle(shuffled)
        for schedule in [shuffled, list(reversed(lanes)) * 6,
                         [lane for lane in lanes for _ in range(6)]]:
            result = self.lean.run(case, schedule=schedule)
            self.assertEqual(result["status"], "completed")
            self.assertEqual(result["output"], reference(case))
            self.assertTrue(all(a["lane"] < case.tokens for a in result["accesses"]))
            stores = [a for a in result["accesses"] if a["space"] == "output"]
            self.assertEqual(sorted(a["address"] for a in stores), list(range(case.tokens)))
            self.assertTrue(all(a["address"] == a["lane"] for a in stores))

    def test_starvation_and_invalid_lane(self):
        case = GatherCase(2, 3, 4, (0, 1), (10, 11, 20, 21))
        result = self.lean.run(case, schedule=[0] * 30)
        self.assertEqual(result["status"], "incomplete")
        self.assertEqual(result["output"], [10, None, None])
        self.assertEqual(self.lean.run(case, schedule=[4])["fault"],
                         {"kind": "invalid_lane", "lane": 4})

    def test_missing_mask_and_wrong_page(self):
        fixtures = mutation_cases()
        missing = self.lean.run(fixtures["missing_mask"], mutation="missing_mask")
        self.assertEqual(missing["status"], "fault")
        self.assertEqual(missing["fault"]["access"]["space"], "output")
        wrong = self.lean.run(fixtures["wrong_page"], mutation="wrong_page")
        self.assertEqual(wrong["status"], "completed")
        self.assertEqual(wrong["output"], [20, 11, 20, 11])
        self.assertNotEqual(wrong["output"], reference(fixtures["wrong_page"]))

    def test_native_launch_contract(self):
        base = dict(page_size=2, tokens=3, block_size=4, table=(0, 1), cache=(10, 11, 20, 21))
        for change in [dict(page_size=0), dict(tokens=True), dict(tokens=5),
                       dict(table=(0, 2)), dict(cache=(1 << 32,) * 4)]:
            with self.subTest(change=change), self.assertRaises(ValueError):
                GatherCase(**dict(base, **change))
