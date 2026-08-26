import importlib.util
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
SPEC = importlib.util.spec_from_file_location(
    "h7_adaptive", HERE / "generate_h7_adaptive_binary_tree_jobs.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class GenerateH7AdaptiveBinaryTreeJobsTest(unittest.TestCase):
    def test_branch_specific_depth_three_tree(self):
        raw = {"": 1280, "0": 1279, "1": 1279,
               "00": 1278, "01": 1314, "10": 1313, "11": 1312}
        nodes = MOD.validate_nodes(raw, 30646, [1254, 1254])
        leaves = MOD.expected_leaves("parent", nodes, [1254, 1254])
        self.assertEqual([leaf["path"] for leaf in leaves],
                         ["000", "001", "010", "011",
                          "100", "101", "110", "111"])
        leaf011 = next(leaf for leaf in leaves if leaf["path"] == "011")
        self.assertEqual(leaf011["units"],
                         [1254, 1254, -1280, 1279, 1314])

    def test_rejects_orphan_and_repeated_path_variable(self):
        with self.assertRaisesRegex(ValueError, "no internal parent"):
            MOD.validate_nodes({"": 1280, "00": 1278}, 30646, [1254])
        with self.assertRaisesRegex(ValueError, "already fixed"):
            MOD.validate_nodes({"": 1280, "0": 1280}, 30646, [1254])
        with self.assertRaisesRegex(ValueError, "already fixed"):
            MOD.validate_nodes({"": 1254}, 30646, [1254])


if __name__ == "__main__":
    unittest.main()
