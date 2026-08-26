import importlib.util
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
SPEC = importlib.util.spec_from_file_location(
    "h7_adaptive_binary_lean", HERE / "generate_h7_adaptive_binary_tree_lean.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class GenerateH7AdaptiveBinaryTreeLeanTest(unittest.TestCase):
    def setUp(self):
        self.parent_id = "h7_t0_cube1.cube-0-0"
        self.nodes = {"": 1280, "0": 1279, "1": 1314, "00": 1278}

    def test_branch_cnf_uses_branch_specific_variables_and_signs(self):
        self.assertEqual(
            MOD.branch_cnf("base", self.nodes, "001"),
            "cnfWithSignedUnit (cnfWithSignedUnit "
            "(cnfWithSignedUnit (base) 1279 false) 1278 false) 1277 true")
        self.assertEqual(
            MOD.branch_cnf("base", self.nodes, "10"),
            "cnfWithSignedUnit (cnfWithSignedUnit (base) 1279 true) 1313 false")

    def test_tree_expression_preserves_adaptive_shape(self):
        rendered = MOD.tree_expression(self.parent_id, self.nodes)
        self.assertIn(".split 1279 (.split 1278 (.split 1277", rendered)
        self.assertIn("(.split 1313", rendered)
        for path in ("000", "001", "01", "10", "11"):
            self.assertIn(
                f"{MOD.lean_stem(self.parent_id + '.adaptive.leaf-' + path)}Unsat",
                rendered)

    def test_render_exports_uniform_binary_unsat_interface(self):
        leaves = [
            {"id": f"{self.parent_id}.adaptive.leaf-{path}", "path": path}
            for path in ("000", "001", "01", "10", "11")
        ]
        manifest = {
            "parent_id": self.parent_id, "nodes": self.nodes, "leaves": leaves,
        }
        parent = {"kind": "cube", "left_index": 0, "right_index": 0}
        payloads = {leaf["id"]: f"certs/{leaf['id']}.lrat" for leaf in leaves}
        rendered = MOD.render(manifest, parent, payloads)
        self.assertEqual(rendered.count("native_decide"), len(leaves))
        self.assertIn("H7T0Cube1Cube00BinaryUnsat", rendered)
        self.assertIn("CnfBinaryCheckedTree.unsat", rendered)
        self.assertIn("AdaptiveBinaryTree", rendered)


if __name__ == "__main__":
    unittest.main()
