import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
SPEC = importlib.util.spec_from_file_location(
    "h7_empty_adaptive_lean",
    HERE / "generate_h7_empty_cube_adaptive_lean.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class GenerateH7EmptyCubeAdaptiveLeanTest(unittest.TestCase):
    def test_receipts_are_strict_complete_paths(self):
        zero, one = "0" * 64, "1" * 64
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "receipts.tsv"
            path.write_text(
                f"cube_F6_t2.adaptive.leaf-00 {zero} {one} 123\n"
                f"cube_F6_t2.adaptive.leaf-11 {one} {zero} 456\n")
            rows = MOD.read_receipts(path)
            self.assertEqual(rows["cube_F6_t2.adaptive.leaf-00"]["path"], "00")
            path.write_text(f"cube_F6_t2.adaptive.leaf-x {zero} {one} 123\n")
            with self.assertRaisesRegex(ValueError, "malformed adaptive receipt"):
                MOD.read_receipts(path)

    def test_render_emits_branch_specific_checked_tree(self):
        nodes = {"": 41, "0": 40, "1": 36}
        leaves = MOD.adaptive.trees.expected_leaves(
            "cube_F6_t2", nodes, list(range(1, 22)))
        manifest = {"parent_id": "cube_F6_t2", "edge_count": 6,
                    "type_index": 2}
        includes = {leaf["id"]: f"proofs/{leaf['path']}.lrat"
                    for leaf in leaves}
        rendered = MOD.render(manifest, nodes, leaves, includes)
        self.assertEqual(rendered.count("native_decide"), 4)
        self.assertIn("cnfWithSignedUnit (cnfWithSignedUnit", rendered)
        self.assertIn(".split 40", rendered)
        self.assertIn(".split 39", rendered)
        self.assertIn(".split 35", rendered)
        self.assertEqual(rendered.count(".leaf (LRAT.check_sound"), 4)
        self.assertIn(".binaryTree", rendered)
        self.assertIn("h7EmptyAdaptiveEvidenceF6T2", rendered)


if __name__ == "__main__":
    unittest.main()
