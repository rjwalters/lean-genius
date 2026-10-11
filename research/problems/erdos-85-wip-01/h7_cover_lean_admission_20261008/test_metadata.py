"""Small source/inventory/host-guard tests; no Lean, solver, or finite search."""

from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

import common as c


class MetadataTests(unittest.TestCase):
    def test_inventory_and_names_are_complete_and_unique(self):
        cases = [c.select(name) for name in c.hc.CUBES]
        self.assertEqual(len(cases), 28)
        self.assertEqual(len({c.filename(case) for case in cases}), 28)
        self.assertEqual(len({c.namespace(case) for case in cases}), 28)
        self.assertEqual(sum(case["leaves"] for case in cases), 377776)

    def test_f6_template_matches_the_verified_pilot(self):
        case = c.select("cube_F6_t5")
        path = "/workspace/proofs/proof.lrat7"
        expected = c.pilot.lean_source(path, 9870017).replace(
            "Erdos85.HsbCoverPilot.F6T5", c.namespace(case))
        self.assertEqual(c.lean_source(case, path, 9870017), expected)

    def test_each_cube_targets_its_own_formula_and_exports(self):
        for name in c.hc.CUBES:
            with self.subTest(cube=name):
                case = c.select(name)
                f, t = case["edge_count"], case["type_index"]
                source = c.lean_source(case, "/workspace/proofs/proof.lrat7", 1)
                self.assertIn(f"sevenHighT0CanonicalEmptyRepresentativeMask {f} {t}", source)
                self.assertIn(f"orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf 3 {f} {t}", source)
                self.assertIn(f"SevenHighT0CanonicalHsbCoverChecked 3 {f} {t} leafRows", source)
                self.assertEqual(source.count("#print axioms "), 2)
                self.assertIn(f"#print axioms {c.namespace(case)}.checkedCover", source)

    def test_unknown_cube_and_changed_freeze_are_refused(self):
        with self.assertRaisesRegex(ValueError, "Unknown structural cube"):
            c.select("cube_F6_t999")
        with patch.object(c, "INPUT_SHA", "0" * 64):
            with self.assertRaisesRegex(ValueError, "Changed frozen input"):
                c.inventory()

    def test_unsafe_source_paths_and_unbounded_proofs_are_refused(self):
        case = c.select("cube_F7_t14")
        for path in ['/tmp/proof', '/workspace/proof"\naxiom bad : False', '/workspace/proof\\bad']:
            with self.subTest(path=path), self.assertRaises(ValueError):
                c.lean_source(case, path, 1)
        for size in [0, -1, (64 << 20) + 1, True]:
            with self.subTest(size=size), self.assertRaises(ValueError):
                c.lean_source(case, "/workspace/proof", size)

    def test_prior_pilot_is_bound_to_the_same_freeze(self):
        self.assertEqual(c.pilot_reuse()["cube"], "cube_F6_t5")
        self.assertEqual(c.pilot_reuse()["olean_sha256"],
                         "91b3f8e93b6a73244450cfbbc0848866157f5a42ab88a5f76a7cf5d9e3bc7500")

    @unittest.skipIf(sys.platform == "linux" and Path("/opt/e85/jobs").is_dir(),
                     "Host-refusal test is intended for the local development machine")
    def test_compute_commands_refuse_local_execution_before_inputs(self):
        commands = [
            ["produce.py", "--cube", "cube_F6_t8", "--inputs", "/missing",
             "--input-manifest-sha256", c.INPUT_SHA, "--output", "/missing"],
            ["check.py", "--production", "/missing", "--production-receipt-sha256",
             "0" * 64, "--output", "/missing"],
        ]
        for script, *args in commands:
            with self.subTest(script=script):
                result = subprocess.run([sys.executable, str(c.PACKAGE / script), *args],
                                        text=True, capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Run only", result.stderr)
                self.assertNotIn("FileNotFoundError", result.stderr)


if __name__ == "__main__":
    unittest.main()
