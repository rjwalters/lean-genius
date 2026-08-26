#!/usr/bin/env python3

import importlib.util
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "h7_t0_empty_quotient", HERE / "check_h7_t0_empty_quotient.py")
MOD = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = MOD
SPEC.loader.exec_module(MOD)


class CheckH7T0EmptyQuotientTest(unittest.TestCase):
    def test_complete_labeled_search_is_unsatisfiable(self):
        result = MOD.run_search()
        self.assertFalse(result.satisfiable)
        self.assertEqual(result.tested_graphs, 1_047_014)
        self.assertEqual(result.filtered_graphs, 20_730)
        self.assertEqual(
            result.filtered_by_edges,
            {4: 0, 5: 0, 6: 0, 7: 360, 8: 17_010, 9: 3_360, 10: 0},
        )


if __name__ == "__main__":
    unittest.main()
