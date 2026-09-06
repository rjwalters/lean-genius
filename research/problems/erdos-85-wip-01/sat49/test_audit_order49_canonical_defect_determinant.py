"""Exact regression checks for the necessary square-root trace test."""

import itertools
import unittest

import sympy as sp

from audit_order49_canonical_defect_determinant import (
    residual_square_root_trace_possible,
)


class SquareRootTraceTests(unittest.TestCase):
    @staticmethod
    def squared_with_residual(*roots):
        # The first four coordinates supply x^2*(x^2-43*x+9).
        root = sp.diag(sp.zeros(2), sp.Matrix([[3, 3], [3, 4]]), *roots)
        return root, (root * root).tolist()

    def test_mixed_copies_preserve_actual_zero_trace_root(self):
        root, square = self.squared_with_residual(4, -4, -7)
        self.assertEqual(root, root.T)
        self.assertEqual(sp.trace(root), 0)
        possible, reason, traces = residual_square_root_trace_possible(square)
        self.assertTrue(possible)
        self.assertEqual(reason, "success")
        self.assertEqual(traces, (-15, -7, -1, 1, 7, 15))

    def test_all_multiplicities_match_explicit_diagonal_roots(self):
        _, square = self.squared_with_residual(4, 4, 4, 7)
        expected = tuple(sorted({
            sum(sign * value for sign, value in zip(signs, (4, 4, 4, 7)))
            for signs in itertools.product((-1, 1), repeat=4)
        }))
        _, _, traces = residual_square_root_trace_possible(square, target_trace=0)
        self.assertEqual(traces, expected)
        self.assertNotIn(0, traces)

    def test_unpaired_irrational_root_remains_impossible(self):
        _, forced = self.squared_with_residual()
        square = sp.diag(sp.Matrix(forced), 2).tolist()
        possible, reason, _ = residual_square_root_trace_possible(square)
        self.assertFalse(possible)
        self.assertEqual(reason, "odd_self_factor_degree_2_exp_1")


if __name__ == "__main__":
    unittest.main()
