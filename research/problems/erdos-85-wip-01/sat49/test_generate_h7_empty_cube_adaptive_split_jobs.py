import importlib.util
import json
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
SPEC = importlib.util.spec_from_file_location(
    "h7_empty_adaptive",
    HERE / "generate_h7_empty_cube_adaptive_split_jobs.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MOD)


class GenerateH7EmptyCubeAdaptiveSplitJobsTest(unittest.TestCase):
    def test_eight_leaf_shape_matches_bounded_f6_t2_signal(self):
        spec = json.loads((HERE / "h7-empty-cube-F6-t2-adaptive-spec.json").read_text())
        self.assertEqual(spec["schema"], MOD.SPEC_SCHEMA)
        self.assertEqual(spec["parent_id"], "cube_F6_t2")
        nodes = MOD.trees.validate_nodes(
            spec["nodes"], 17633, list(range(1, 22)))
        leaves = MOD.trees.expected_leaves(
            "cube_F6_t2", nodes, list(range(1, 22)))
        self.assertEqual([leaf["path"] for leaf in leaves],
                         ["000", "001", "010", "011",
                          "100", "101", "110", "111"])
        self.assertEqual(
            [leaf["path_units"] for leaf in leaves],
            [[-41, -40, -81], [-41, -40, 81],
             [-41, 40, -37], [-41, 40, 37],
             [41, -36, -33], [41, -36, 33],
             [41, 36, -27], [41, 36, 27]])

    def test_rejects_parent_fixed_or_repeated_split(self):
        with self.assertRaisesRegex(ValueError, "already fixed"):
            MOD.trees.validate_nodes({"": 3}, 17633, [1, 2, 3])
        with self.assertRaisesRegex(ValueError, "already fixed"):
            MOD.trees.validate_nodes({"": 41, "0": 41}, 17633, [1, 2, 3])


if __name__ == "__main__":
    unittest.main()
