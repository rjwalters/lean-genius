#!/usr/bin/env python3

import unittest

import generate_h7_empty_cube_split_jobs as splits


class H7EmptyCubeSplitJobsTest(unittest.TestCase):
    def test_choose_split_uses_two_sided_rank(self) -> None:
        clauses = [(1, 2), (-1, 3), (-3, 4)]
        occurrence = {}
        for index, clause in enumerate(clauses):
            for literal in clause:
                occurrence.setdefault(literal, []).append(index)
        result = splits.choose_split(clauses, occurrence, [], candidate_max=4)
        self.assertEqual(result["variable"], 1)
        self.assertTrue(result["false"]["consistent"])
        self.assertTrue(result["true"]["consistent"])
        self.assertGreaterEqual(result["false"]["forced"], 1)
        self.assertGreaterEqual(result["true"]["forced"], 1)

    def test_no_candidate_after_parent_fixes_all(self) -> None:
        clauses = [(1, 2)]
        occurrence = {1: [0], 2: [0]}
        with self.assertRaisesRegex(ValueError, "no unfixed"):
            splits.choose_split(clauses, occurrence, [1, 2], candidate_max=2)


if __name__ == "__main__":
    unittest.main()
