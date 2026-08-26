import importlib.util
import sys
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
SPEC = importlib.util.spec_from_file_location(
    "h1_aggregate", HERE / "generate_h1_v2_lean_aggregate.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)
ROW = MOD.IndexRow(
    "0000000000000000", 0, 0, *("0" * 64 for _ in range(3)),
    None, 1, 1, True, "0" * 64, 1, "0" * 64, 1, "0" * 64, 1,
)


class GenerateH1V2LeanAggregateTest(unittest.TestCase):
    def test_complete_coverage_validation(self):
        profiles = [[f"{profile:016x}"] for profile in range(5)]
        rows = [
            replace(ROW, orbit=profiles[profile][0], profile=profile)
            for profile in range(5)
        ]
        MOD.validate_complete(rows, profiles)
        with self.assertRaisesRegex(ValueError, "requires all"):
            MOD.validate_complete(rows[:-1], profiles)
        with self.assertRaisesRegex(ValueError, "does not exactly cover"):
            MOD.validate_complete([replace(rows[0], orbit="f" * 16)] + rows[1:], profiles)
        with self.assertRaisesRegex(ValueError, "not stub_ready"):
            MOD.validate_complete([replace(rows[0], stub_ready=False)] + rows[1:], profiles)

    def test_render_has_ordered_banks_and_final_h1_endpoint(self):
        rows = [replace(ROW, profile=profile) for profile in range(5)]
        rendered = MOD.aggregate_source(rows, "Proofs.Generated.H1")
        self.assertEqual(rendered.count("import Proofs.Generated.H1."), 5)
        self.assertIn("h1V2P3I00000Entry", rendered)
        self.assertEqual(rendered.count("_covers :"), 5)
        self.assertNotIn("native_decide", rendered)
        self.assertEqual(rendered.count("  rfl\n"), 5)
        self.assertEqual(rendered.count("set_option maxHeartbeats 0 in"), 5)
        self.assertEqual(rendered.count("set_option maxRecDepth 1000000 in"), 5)
        self.assertIn(
            "orderFortyNineStratumExcluded_one_of_completeV2Certificates",
            rendered)
        self.assertIn("· exact h1V2InventoryProfile4_checked", rendered)

    def test_stub_sources_must_exist_with_exact_entry(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            path = root / "Erdos85H1V2CertP0I00000.lean"
            with self.assertRaisesRegex(ValueError, "missing generated"):
                MOD.validate_stub_sources([ROW], root)
            path.write_text("theorem wrong\n")
            with self.assertRaisesRegex(ValueError, "wrong declarations"):
                MOD.validate_stub_sources([ROW], root)
            path.write_text(
                "theorem h1V2P0I00000Checked : True := True.intro\n"
                "def h1V2P0I00000Entry : OneHighFamilyV2CheckedEntry 0 := x\n"
            )
            MOD.validate_stub_sources([ROW], root)


if __name__ == "__main__":
    unittest.main()
