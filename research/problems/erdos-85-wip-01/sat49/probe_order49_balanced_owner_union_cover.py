#!/usr/bin/env python3
"""Test one-sided owner-union cuts in the balanced transport dual."""

from __future__ import annotations

import argparse

import numpy as np
import z3
from scipy.optimize import Bounds, LinearConstraint, milp

from extract_order49_two_color_farkas import primal_matrices
from probe_order49_three_open_code_holonomy import (
    CODES, PAIR01, PAIR02, PAIR12, build_solver, support,
)


def best_balanced_owner_union(owner: list[list[int]], selected: set[int]):
    _, demand, cover, capacity, pairs, degree_names, cap_names = primal_matrices(
        owner, selected
    )
    zeros = [name[1] for name in degree_names]
    zero_index = {z: i for i, z in enumerate(zeros)}
    pair_index = {pair: i for i, pair in enumerate(pairs)}
    owner_bits = [
        u for h in range(3) for u in CODES[h] if support(u) == 1
    ]
    bit_index = {u: i for i, u in enumerate(owner_bits)}
    bit_count, alpha_count, cap_count = len(owner_bits), len(zeros), len(capacity)
    alpha_offset = bit_count
    row_offset = alpha_offset + alpha_count
    column_offset = row_offset + cap_count
    variable_count = column_offset + cap_count
    rows, lower, upper = [], [], []

    def constraint(entries, lo=-np.inf, hi=np.inf):
        row = np.zeros(variable_count)
        for index, coefficient in entries:
            row[index] += coefficient
        rows.append(row)
        lower.append(lo)
        upper.append(hi)

    # alpha is exactly the OR of all selected singleton-owner fibers.
    for zi, z in enumerate(zeros):
        incident = [
            bit_index[owner[h][z]] for h in range(3)
            if owner[h][z] in bit_index
        ]
        for bit in incident:
            constraint(((alpha_offset + zi, 1), (bit, -1)), lo=0)
        constraint(
            [(alpha_offset + zi, 1)] + [(bit, -1) for bit in incident], hi=0
        )

    # Only column degree multipliers are active.  Row cap i covers z -> w;
    # its transpose copy covers w -> z.
    for v in zeros:
        for w in zeros:
            if v == w:
                continue
            pair = pair_index[min(v, w), max(v, w)]
            entries = [(alpha_offset + zero_index[w], 1)]
            for i, (_, center, _) in enumerate(cap_names):
                coefficient = cover[i, pair]
                if not coefficient:
                    continue
                if center == v:
                    entries.append((row_offset + i, -coefficient))
                if center == w:
                    entries.append((column_offset + i, -coefficient))
            constraint(entries, hi=0)

    objective = np.r_[
        np.zeros(bit_count), -demand, capacity, capacity
    ]
    result = milp(
        objective,
        integrality=np.r_[
            np.ones(bit_count + alpha_count), np.zeros(2 * cap_count)
        ],
        bounds=Bounds(
            np.zeros(variable_count),
            np.r_[
                np.ones(bit_count + alpha_count),
                np.full(2 * cap_count, np.inf),
            ],
        ),
        constraints=LinearConstraint(np.asarray(rows), lower, upper),
    )
    if not result.success:
        return None
    bits = result.x[:bit_count]
    alpha = result.x[alpha_offset:row_offset]
    row_weights = result.x[row_offset:column_offset]
    column_weights = result.x[column_offset:]
    subsets = tuple(
        tuple(u for u in CODES[h] if u in bit_index and bits[bit_index[u]] > 0.5)
        for h in range(3)
    )
    demand_total = float(alpha @ demand)
    capacity_total = float(row_weights @ capacity + column_weights @ capacity)
    return (
        demand_total - capacity_total, subsets, int(round(alpha.sum())),
        demand_total, capacity_total,
        int(np.sum(row_weights > 1e-8)), int(np.sum(column_weights > 1e-8)),
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=("000", "001"), required=True)
    parser.add_argument("--samples", type=int, default=16)
    parser.add_argument("--require", action="store_true")
    args = parser.parse_args()
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
        owner = [
            [model.eval(variables[h][v]).as_long() for v in range(46)]
            for h in range(3)
        ]
        best = best_balanced_owner_union(owner, {0, 1})
        print(f"sample={sample} profile={args.profile} best={best}")
        if args.require and (best is None or best[0] <= 1e-8):
            raise RuntimeError("no deficient one-sided owner-union cover")
        solver.add(z3.Or(*(
            variables[h][v] != owner[h][v]
            for h in range(3) for v in range(46)
        )))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
