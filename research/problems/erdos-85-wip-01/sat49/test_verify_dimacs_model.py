import tempfile
import unittest
from pathlib import Path

from verify_dimacs_model import VerificationError, verify


class VerifyDimacsModelTest(unittest.TestCase):
    def check(self, cnf: str, model: str) -> tuple[int, int, str, str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cnf_path, model_path = root / "input.cnf", root / "model.out"
            cnf_path.write_text(cnf, encoding="ascii")
            model_path.write_text(model, encoding="ascii")
            return verify(cnf_path, model_path)

    def test_accepts_complete_multiline_model_and_clause(self) -> None:
        variables, clauses, _, _ = self.check(
            "c test\np cnf 3 2\n1 -2\n0\n-1 3 0\n",
            "c solver output\ns SATISFIABLE\nv 1 -2\nv 3 0\n",
        )
        self.assertEqual((variables, clauses), (3, 2))

    def test_rejects_unsatisfied_clause(self) -> None:
        with self.assertRaisesRegex(VerificationError, "clause 2"):
            self.check("p cnf 2 2\n1 0\n2 0\n", "s SATISFIABLE\nv 1 -2 0\n")

    def test_rejects_incomplete_assignment(self) -> None:
        with self.assertRaisesRegex(VerificationError, "not complete"):
            self.check("p cnf 3 1\n1 0\n", "s SATISFIABLE\nv 1 -2 0\n")

    def test_rejects_duplicate_assignment(self) -> None:
        with self.assertRaisesRegex(VerificationError, "duplicate assignment"):
            self.check("p cnf 2 1\n1 0\n", "s SATISFIABLE\nv 1 -1 2 0\n")

    def test_rejects_unterminated_or_post_terminator_assignment(self) -> None:
        with self.assertRaisesRegex(VerificationError, "unterminated"):
            self.check("p cnf 1 1\n1 0\n", "s SATISFIABLE\nv 1\n")
        with self.assertRaisesRegex(VerificationError, "after model terminator"):
            self.check("p cnf 2 1\n1 0\n", "s SATISFIABLE\nv 1 0\nv 2 0\n")

    def test_rejects_bad_status_and_clause_count(self) -> None:
        with self.assertRaisesRegex(VerificationError, "not SATISFIABLE"):
            self.check("p cnf 1 1\n1 0\n", "s UNKNOWN\nv 1 0\n")
        with self.assertRaisesRegex(VerificationError, "declares 2 clauses"):
            self.check("p cnf 1 2\n1 0\n", "s SATISFIABLE\nv 1 0\n")

    def test_accepts_empty_formula(self) -> None:
        variables, clauses, _, _ = self.check("p cnf 0 0\n", "s SATISFIABLE\nv 0\n")
        self.assertEqual((variables, clauses), (0, 0))


if __name__ == "__main__":
    unittest.main()
