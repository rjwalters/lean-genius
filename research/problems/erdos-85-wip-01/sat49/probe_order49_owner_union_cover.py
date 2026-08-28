#!/usr/bin/env python3
"""Search row/column-union cuts in the two-color fractional obstruction."""

from __future__ import annotations

import argparse

import numpy as np
import z3
from scipy.optimize import linprog

from extract_order49_two_color_farkas import primal_matrices
from probe_order49_three_open_code_holonomy import (
    CODES, PAIR01, PAIR02, PAIR12, build_solver, support,
)


def best_union_cover(owner: list[list[int]], selected: tuple[int, int]):
    _, demand, cover, capacity, pairs, degree_names, _ = primal_matrices(
        owner, set(selected)
    )
    zeros = [name[1] for name in degree_names]
    zero_index = {z: i for i, z in enumerate(zeros)}
    groups = [[u for u in CODES[h] if support(u) == 1] for h in selected]
    best = None
    for left_mask in range(1 << len(groups[0])):
        left = {u for i, u in enumerate(groups[0]) if left_mask >> i & 1}
        for right_mask in range(1 << len(groups[1])):
            right = {u for i, u in enumerate(groups[1]) if right_mask >> i & 1}
            alpha = np.asarray([
                int(owner[selected[0]][z] in left or owner[selected[1]][z] in right)
                for z in zeros
            ])
            if not alpha.any():
                continue
            edge_demand = np.asarray([
                alpha[zero_index[v]] + alpha[zero_index[w]] for v, w in pairs
            ])
            result = linprog(
                capacity, A_ub=-cover.T, b_ub=-edge_demand,
                bounds=(0, None), method="highs",
            )
            if result.success:
                degree_total = int(alpha @ demand)
                candidate = (
                    degree_total - float(result.fun), tuple(sorted(left)),
                    tuple(sorted(right)), int(alpha.sum()), degree_total,
                    float(result.fun), int(np.sum(result.x > 1e-8)),
                )
                if best is None or candidate[0] > best[0] + 1e-8:
                    best = candidate
    return best


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=2)
    parser.add_argument("--codes", default="0,1")
    parser.add_argument("--profile", choices=("000", "001"), required=True)
    parser.add_argument("--require", action="store_true")
    args = parser.parse_args()
    selected = tuple(int(value) for value in args.codes.split(","))

    solver, variables = build_solver()
    edges = (
        variables[0][PAIR01] == PAIR02,
        variables[1][PAIR01] == PAIR12,
        variables[2][PAIR02] == PAIR12,
    )
    if args.profile == "000":
        solver.add(*(z3.Not(edge) for edge in edges))
    else:
        solver.add(z3.Not(edges[0]), edges[1], z3.Not(edges[2]))

    for sample in range(args.samples):
        if solver.check() != z3.sat:
            break
        model = solver.model()
        owner = [[model.eval(variables[h][v]).as_long() for v in range(46)] for h in range(3)]
        best = best_union_cover(owner, selected)
        print(f"sample={sample} profile={args.profile} best={best}")
        if args.require and (best is None or best[0] <= 1e-8):
            raise RuntimeError("no deficient row/column-union cover")
        solver.add(z3.Or(*(
            variables[h][v] != owner[h][v]
            for h in range(3) for v in range(46)
        )))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
