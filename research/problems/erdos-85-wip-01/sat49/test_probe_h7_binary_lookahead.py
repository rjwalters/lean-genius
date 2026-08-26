import importlib.util
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "binary_lookahead", HERE / "probe_h7_binary_lookahead.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class BinaryLookaheadTest(unittest.TestCase):
    def test_unit_propagation_and_conflict(self):
        clauses = [(1, 2), (-1, 3), (-3,)]
        occurrence = {}
        for index, clause in enumerate(clauses):
            for literal in clause:
                occurrence.setdefault(literal, []).append(index)
        consistent, assignment = MOD.propagate(
            clauses, occurrence, (-3,))
        self.assertTrue(consistent)
        self.assertEqual(assignment, {3: False, 1: False, 2: True})
        self.assertFalse(MOD.propagate(
            clauses, occurrence, (1, -3))[0])

    def test_dimacs_header_count_is_checked(self):
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "bad.cnf"
            path.write_text("p cnf 2 2\n1 0\n")
            with self.assertRaisesRegex(ValueError, "clause count"):
                MOD.read_dimacs(path)


if __name__ == "__main__":
    unittest.main()
