import importlib.util
import hashlib
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location("materialize", Path(__file__).with_name("materialize_verdict_input.py"))
m = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(m)


class DimacsBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / "input.cnf"

    def write(self, text):
        self.path.write_text(text)
        return self.path

    def test_valid_emitter_lines_and_empty_clause_are_counted(self):
        result = m.validate_dimacs(self.write("c example\np cnf 2 3\n1 -2 0\n0\n2 0\n"))
        self.assertEqual((result["variables"], result["clauses"]), (2, 3))

    def test_legacy_comparator_clause_boundary_counterexample(self):
        with self.assertRaisesRegex(ValueError, "one clause per line"):
            m.validate_emitter_match(self.write("p cnf 2 2\n1\n2 0 0\n"), 0,
                                     "MATCH (2 clauses, top 2)\n")

    def test_internal_zero_and_non_ascii_space_separators_rejected(self):
        for text in ["p cnf 2 2\n1 0 2 0\n", "p cnf 3 1\n1 2\t3 0\n",
                     "p cnf 2 1\n\t1 2 0\n"]:
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, "one clause per line"):
                m.validate_dimacs(self.write(text))

    def test_added_empty_clause_cannot_hide_from_header(self):
        with self.assertRaisesRegex(ValueError, "clause count"):
            m.validate_dimacs(self.write("p cnf 1 1\n1 0\n0\n"))

    def test_changed_header_cannot_hide_empty_clause_from_match(self):
        with self.assertRaisesRegex(ValueError, "generator MATCH"):
            m.validate_emitter_match(self.write("p cnf 1 2\n1 0\n0\n"), 0,
                                     "MATCH (1 clauses, top 1)\n")

    def test_malformed_dimacs_is_rejected(self):
        for text in ["1 0\n", "p cnf 1 1\n2 0\n", "p cnf 1 1\n1\n",
                     "p cnf 1 0\np cnf 1 0\n", "p cnf 1 1\nabc 0\n"]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                m.validate_dimacs(self.write(text))

    def test_match_requires_success_and_exact_output(self):
        self.write("p cnf 1 1\n1 0\n")
        m.validate_emitter_match(self.path, 0, "MATCH (1 clauses, top 1)\n")
        for rc, output in [(1, "MATCH (1 clauses, top 1)"), (0, "MATCH"),
                           (0, "MATCH (1 clauses, top 1)\nMATCH (1 clauses, top 1)")]:
            with self.assertRaises(ValueError):
                m.validate_emitter_match(self.path, rc, output)

    def test_unit_materialization_preserves_bytes_order_and_duplicates(self):
        base = b"c before\np cnf 2 1\n1 -2 0\nc after\n"
        self.path.write_bytes(base)
        output = self.path.with_name("root.cnf")
        expected = base.replace(b"p cnf 2 1", b"p cnf 2 4") + b"2 0\n2 0\n-1 0\n"
        result = m.materialize_units(self.path, hashlib.sha256(base).hexdigest(), [2, 2, -1],
                                     output, hashlib.sha256(expected).hexdigest(), len(expected), 2, 4)
        self.assertEqual(output.read_bytes(), expected)
        self.assertEqual(result["units"], [2, 2, -1])

    def test_materialization_never_overwrites_existing_input(self):
        base = b"p cnf 1 1\n1 0\n"
        self.path.write_bytes(base)
        output = self.path.with_name("retained.cnf")
        output.write_bytes(b"retained sentinel")
        with self.assertRaises(FileExistsError):
            m.materialize_units(self.path, hashlib.sha256(base).hexdigest(), [], output,
                                 hashlib.sha256(base).hexdigest(), len(base), 1, 1)
        self.assertEqual(output.read_bytes(), b"retained sentinel")

    def test_wrong_base_and_output_hashes_do_not_produce_success(self):
        base = b"p cnf 1 1\n1 0\n"
        self.path.write_bytes(base)
        output = self.path.with_name("root.cnf")
        with self.assertRaisesRegex(ValueError, "Base hash"):
            m.materialize_units(self.path, "0" * 64, [], output,
                                 hashlib.sha256(base).hexdigest(), len(base), 1, 1)
        self.assertFalse(output.exists())
        with self.assertRaisesRegex(ValueError, "reviewed root identity"):
            m.materialize_units(self.path, hashlib.sha256(base).hexdigest(), [], output,
                                 "0" * 64, len(base), 1, 1)

    def test_materialization_rejects_oversize_before_writing(self):
        output = self.path.with_name("root.cnf")
        with self.assertRaisesRegex(ValueError, "99 MB"):
            m.materialize_units(self.path, "0" * 64, [], output, "0" * 64,
                                 m.MAX_INPUT_BYTES + 1, 1, 1)
        self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
