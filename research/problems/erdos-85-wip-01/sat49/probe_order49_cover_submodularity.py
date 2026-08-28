#!/usr/bin/env python3
"""Reproduce failures of sub- and supermodularity for the cap-cover value."""

from __future__ import annotations

import math

import numpy as np
import z3
from scipy.optimize import linprog

from extract_order49_two_color_farkas import primal_matrices
from probe_order49_three_open_code_holonomy import build_solver


def main() -> int:
    solver, variables = build_solver()
    if solver.check() != z3.sat:
        raise RuntimeError("owner model unavailable")
    model = solver.model()
    owner = [[model.eval(variables[h][v]).as_long() for v in range(46)] for h in range(3)]
    _, demand, cover, capacity, pairs, degree_names, _ = primal_matrices(owner, {0, 1})
    zeros = [name[1] for name in degree_names]
    zero_index = {z: i for i, z in enumerate(zeros)}

    def value(selected: set[int]) -> float:
        alpha = np.asarray([int(z in selected) for z in zeros])
        edge_demand = np.asarray([
            alpha[zero_index[v]] + alpha[zero_index[w]] for v, w in pairs
        ])
        result = linprog(
            capacity, A_ub=-cover.T, b_ub=-edge_demand,
            bounds=(0, None), method="highs",
        )
        return float(result.fun - alpha @ demand) if result.success else math.inf

    def four_values(left: set[int], right: set[int]):
        return tuple(value(s) for s in (left, right, left | right, left & right))

    sub = four_values({22, 30, 38, 45}, {23, 26, 41, 45})
    sup = four_values({29, 32, 40, 41}, {24, 25, 26, 31, 44})
    print(f"submodularity_counterexample {sub}")
    print(f"supermodularity_counterexample {sup}")
    if not sub[0] + sub[1] < sub[2] + sub[3]:
        raise RuntimeError("expected strict submodularity violation disappeared")
    if not sup[0] + sup[1] > sup[2] + sup[3]:
        raise RuntimeError("expected strict supermodularity violation disappeared")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
