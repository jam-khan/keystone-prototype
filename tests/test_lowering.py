"""Source, flat IR, and emitted native code; the CUDA scope stays explicit."""
from pathlib import Path
import tempfile
import unittest

from experiments.gather import cases, reference
from experiments.lowering import LoweredNative, lower, request_for


U64 = (1 << 64) - 1


def request(source, tokens=1, cache=()):
    return dict(source=source, page_size=0, tokens=tokens, lanes=1, table=[], cache=list(cache))


class LoweringTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)

    def agree(self, value, expected=None):
        result = lower(value)
        self.assertTrue(result["lowering_theorem_applies"])
        self.assertEqual(result["source"], result["target"])
        if expected is not None:
            self.assertEqual(result["target"]["status"], "ok")
            self.assertEqual(result["target"]["output"], expected)
            self.assertEqual(LoweredNative(result, directory=self.directory).run(value), expected)
        return result

    def test_gather_source_target_native_and_specification(self):
        native = None
        for case in cases(seed=781, count=12):
            value = request_for(case)
            result = self.agree(value)
            if native is None:
                native = LoweredNative(result, directory=self.directory)
            self.assertEqual(result["target"]["output"], reference(case))
            self.assertEqual(native.run(value), reference(case))

    def test_nested_masks_skip_invalid_reads_and_restore_predicates(self):
        program = {"seq": [
            {"when_lt": [1, 0, {"seq": [
                {"load_cache": [0, U64]},
                {"when_lt": [0, 1, {"load_table": [1, U64]}]}]}]},
            {"when_lt": [0, 1, {"seq": [
                {"when_lt": [5, 2, {"store": [0, 99]}]}, {"store": [0, 42]}]}]}]}
        result = self.agree(request(program), [42])
        self.assertEqual(result["target"]["accesses"], [{"lane": 0, "space": "output", "address": 0}])

    def test_fault_preserves_write_and_access_prefix(self):
        program = {"seq": [{"store": [0, 7]}, {"load_cache": [0, 9]}, {"store": [0, 99]}]}
        value = request(program, cache=[10])
        result = self.agree(value)
        self.assertEqual(result["target"]["status"], "fault")
        self.assertEqual(result["target"]["output"], [7])
        self.assertEqual(len(result["target"]["accesses"]), 1)
        with self.assertRaises(RuntimeError):
            LoweredNative(result, directory=self.directory).run(value)

    def test_word_arithmetic_and_zero_initialized_locals(self):
        expressions = [{"add": [U64, 1]}, {"mul": [U64, 2]},
                       {"div": [123, 0]}, {"mod": [123, 0]}, {"local": 77}]
        program = {"seq": [{"store": [i, expr]} for i, expr in enumerate(expressions)]}
        self.agree(request(program, tokens=5), [0, (1 << 32) - 2, 0, 123, 0])

    def test_lowering_mutations(self):
        missing = lower(dict(request_for(next(cases(count=0))), mutation="drop_masks"))
        self.assertFalse(missing["lowering_theorem_applies"])
        self.assertEqual(missing["target"]["status"], "fault")
        wrong = lower(dict(page_size=2, tokens=4, lanes=4, table=[1, 0],
                           cache=[10, 11, 20, 21], mutation="wrong_division"))
        self.assertFalse(wrong["observable_equivalent"])
        self.assertEqual(wrong["target"]["output"], [20, 11, 20, 11])
        program = {"seq": [{"when_lt": [1, 0, {"skip": True}]}, {"store": [0, 7]}]}
        restore = lower(dict(request(program), mutation="drop_restore"))
        self.assertFalse(restore["observable_equivalent"])

    def test_cuda_scope_and_observable_equivalence_are_not_proofs(self):
        custom = self.agree(request({"store": [0, 1]}))
        invalid = lower(dict(page_size=0, tokens=1, lanes=1, table=[0], cache=[7]))
        for result in [custom, invalid]:
            with self.assertRaises(ValueError):
                LoweredNative(result, cuda=True, directory=self.directory)
        value = request({"when_lt": [0, 1, {"skip": True}]})
        leaked_frame = lower(dict(value, mutation="drop_restore"))
        self.assertTrue(leaked_frame["observable_equivalent"])
        self.assertFalse(leaked_frame["lowering_theorem_applies"])
