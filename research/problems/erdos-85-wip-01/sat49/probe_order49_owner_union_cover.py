#!/usr/bin/env python3
"""Search row/column-union cuts in the two-color fractional obstruction."""

from __future__ import annotations

import argparse

import numpy as np
import z3
from scipy.optimize import Bounds, LinearConstraint, milp

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
    owner_bits = groups[0] + groups[1]
    bit_index = {u: i for i, u in enumerate(owner_bits)}
    bit_count, alpha_count, row_count = len(owner_bits), len(zeros), len(capacity)
    alpha_offset = bit_count
    row_offset = bit_count + alpha_count
    variable_count = row_offset + row_count
    rows, lower, upper = [], [], []

    def constraint(entries, lo=-np.inf, hi=np.inf):
        row = np.zeros(variable_count)
        for index, coefficient in entries:
            row[index] += coefficient
        rows.append(row)
        lower.append(lo)
        upper.append(hi)

    # alpha_z is exactly the disjunction of its selected-color owner bits.
    for zi, z in enumerate(zeros):
        incident = []
        for h in selected:
            owner_value = owner[h][z]
            if owner_value in bit_index:
                incident.append(bit_index[owner_value])
        for bit in incident:
            constraint(((alpha_offset + zi, 1), (bit, -1)), lo=0)
        constraint(
            [(alpha_offset + zi, 1)] + [(bit, -1) for bit in incident], hi=0
        )

    # The weighted cap rows cover alpha at both endpoints of every edge.
    for pair_index, (v, w) in enumerate(pairs):
        entries = [
            (alpha_offset + zero_index[v], 1),
            (alpha_offset + zero_index[w], 1),
        ]
        entries.extend(
            (row_offset + i, -cover[i, pair_index]) for i in range(row_count)
            if cover[i, pair_index]
        )
        constraint(entries, hi=0)

    objective = np.r_[np.zeros(bit_count), -demand, capacity]
    result = milp(
        objective,
        integrality=np.r_[np.ones(bit_count + alpha_count), np.zeros(row_count)],
        bounds=Bounds(
            np.zeros(variable_count),
            np.r_[np.ones(bit_count + alpha_count), np.full(row_count, np.inf)],
        ),
        constraints=LinearConstraint(np.asarray(rows), lower, upper),
    )
    if not result.success:
        return None
    bit_values = result.x[:bit_count]
    alpha = result.x[alpha_offset:row_offset]
    weights = result.x[row_offset:]
    left = tuple(u for u in groups[0] if bit_values[bit_index[u]] > 0.5)
    right = tuple(u for u in groups[1] if bit_values[bit_index[u]] > 0.5)
    degree_total = int(round(alpha @ demand))
    capacity_total = float(weights @ capacity)
    return (
        degree_total - capacity_total, left, right, int(round(alpha.sum())),
        degree_total, capacity_total, int(np.sum(weights > 1e-8)),
    )


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
