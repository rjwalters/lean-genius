#!/usr/bin/env python3
"""Test whether a deficient dual cut can be rainbow in selected owner colors."""

from __future__ import annotations

import argparse

import numpy as np
import z3
from scipy.optimize import Bounds, LinearConstraint, milp

from extract_order49_two_color_farkas import primal_matrices
from probe_order49_three_open_code_holonomy import (
    CODES, PAIR01, PAIR02, PAIR12, build_solver,
)


def rainbow_cut(
    owner: list[list[int]], rainbow_codes: tuple[int, ...], max_fiber: int = 1
):
    _, demand, cover, capacity, pairs, degree_names, _ = primal_matrices(owner, {0, 1})
    zeros = [name[1] for name in degree_names]
    zero_index = {z: i for i, z in enumerate(zeros)}
    alpha_count, row_count = len(zeros), len(capacity)
    objective = np.r_[-demand, capacity]
    constraints, lower, upper = [], [], []
    for pair_index, (v, w) in enumerate(pairs):
        row = np.r_[np.zeros(alpha_count), -cover[:, pair_index]]
        row[zero_index[v]] = 1
        row[zero_index[w]] = 1
        constraints.append(row)
        lower.append(-np.inf)
        upper.append(0)
    for h in rainbow_codes:
        for u in CODES[h]:
            row = np.zeros(alpha_count + row_count)
            for z in zeros:
                if owner[h][z] == u:
                    row[zero_index[z]] = 1
            constraints.append(row)
            lower.append(-np.inf)
            upper.append(max_fiber)
    result = milp(
        objective,
        integrality=np.r_[np.ones(alpha_count), np.zeros(row_count)],
        bounds=Bounds(
            np.zeros(alpha_count + row_count),
            np.r_[np.ones(alpha_count), np.full(row_count, np.inf)],
        ),
        constraints=LinearConstraint(np.asarray(constraints), lower, upper),
    )
    if not result.success:
        return None
    alpha = result.x[:alpha_count]
    weights = result.x[alpha_count:]
    selected = [z for z, value in zip(zeros, alpha) if value > 0.5]
    return (
        -float(result.fun), selected,
        [tuple(owner[h][z] for h in range(3)) for z in selected],
        int(round(alpha @ demand)), float(weights @ capacity),
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=8)
    parser.add_argument("--profile", choices=("000", "001"), required=True)
    parser.add_argument("--rainbow-codes", default="2")
    parser.add_argument("--max-fiber", type=int, default=1)
    parser.add_argument("--require", action="store_true")
    args = parser.parse_args()
    rainbow_codes = tuple(int(value) for value in args.rainbow_codes.split(","))
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
        result = rainbow_cut(owner, rainbow_codes, args.max_fiber)
        print(f"sample={sample} profile={args.profile} rainbow={rainbow_codes} result={result}")
        if args.require and (result is None or result[0] <= 1e-8):
            raise RuntimeError("no deficient rainbow cut")
        solver.add(z3.Or(*(
            variables[h][v] != owner[h][v]
            for h in range(3) for v in range(46)
        )))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
