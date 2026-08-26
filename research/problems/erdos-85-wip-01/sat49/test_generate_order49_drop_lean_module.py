import importlib.util
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "drop_module", HERE / "generate_order49_drop_lean_module.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class GenerateOrder49DropLeanModuleTest(unittest.TestCase):
    def test_render_deduplicates_imports_and_closes_drop(self):
        rendered = MOD.render([
            ("Proofs.Generated.H1", "h1Done"),
            ("Proofs.Generated.SmallHigh", "h3Done"),
            ("Proofs.Generated.SmallHigh", "h5Done"),
            ("Proofs.Generated.H7", "h7Done"),
        ])
        self.assertEqual(rendered.count("import Proofs.Generated.SmallHigh\n"), 1)
        self.assertIn("h1Done h3Done h5Done h7Done", rendered)
        self.assertIn(
            "not_c4FreeMinDegreeWitness_fortyNine_seven_of_generatedCertificates",
            rendered)
        self.assertIn(
            "minDegreeForC4_fortyEight_fortyNine_exact_of_generatedCertificates",
            rendered)
        self.assertIn(
            "minDegreeForC4_fortyNine_lt_fortyEight_of_generatedCertificates",
            rendered)


if __name__ == "__main__":
    unittest.main()
