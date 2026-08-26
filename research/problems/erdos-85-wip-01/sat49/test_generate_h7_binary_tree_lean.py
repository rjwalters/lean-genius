import importlib.util
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
SPEC = importlib.util.spec_from_file_location(
    "h7_binary_lean", HERE / "generate_h7_binary_tree_lean.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class GenerateH7BinaryTreeLeanTest(unittest.TestCase):
    def test_depth_two_render_matches_four_paths(self):
        parent_id = "h7_t0_cube1.cube-0-0"
        manifest = {
            "parent_id": parent_id,
            "split_variables": [1280, 1279],
            "leaves": [
                {"id": f"{parent_id}.binary.leaf-{suffix}", "bits": bits}
                for suffix, bits in (
                    ("00", [False, False]), ("01", [False, True]),
                    ("10", [True, False]), ("11", [True, True]))
            ],
        }
        parent = {"kind": "cube", "left_index": 0, "right_index": 0}
        payloads = {leaf["id"]: f"certs/{leaf['id']}.lrat"
                    for leaf in manifest["leaves"]}
        rendered = MOD.render(manifest, parent, payloads)
        self.assertEqual(rendered.count("native_decide"), 4)
        self.assertIn(
            "cnfWithSignedUnit (cnfWithSignedUnit "
            "(sevenHighT0CubeOnePositiveCnf", rendered)
        self.assertIn(
            ".split 1279 (.split 1278 ", rendered)
        self.assertIn("H7T0Cube1Cube00BinaryUnsat", rendered)
        self.assertIn("CnfBinaryCheckedTree.unsat", rendered)

    def test_dimacs_variables_become_zero_based_lean_variables(self):
        self.assertEqual(
            MOD.branch_cnf("base", [1280, 1279], [False, True]),
            "cnfWithSignedUnit (cnfWithSignedUnit (base) 1279 false) 1278 true")


if __name__ == "__main__":
    unittest.main()
