#!/usr/bin/env python3
"""Optimize canonical fractional covers at two-color hole endpoints.

The selected degree cut is not an arbitrary dual artifact: it is the
support-zero owner fiber N_Z(u) of a two-color hole endpoint u.  This probe
fixes that cut and optimizes only the nonnegative common-neighbor-cap weights.
"""

from __future__ import annotations

import argparse

import numpy as np
import z3
from scipy.optimize import linprog

from extract_order49_two_color_farkas import primal_matrices
from probe_order49_three_open_code_holonomy import (
    CODES, PAIR01, PAIR02, PAIR12, build_solver, support,
)


def holes(owner: list[list[int]], selected: tuple[int, int]) -> list[tuple[int, int]]:
    pairpoints = {0, 1, 2}
    groups = [tuple(v for v in CODES[h] if support(v) == 1) for h in selected]
    realized = {
        (owner[selected[0]][v], owner[selected[1]][v])
        for v in range(46)
        if not ({owner[h][v] for h in selected} & pairpoints)
    }
    return [(a, b) for a in groups[0] for b in groups[1] if (a, b) not in realized]


def endpoint_cover(
    owner: list[list[int]], selected: tuple[int, int], endpoint: int
) -> tuple[float, int, float, int] | None:
    aeq, beq, aub, bub, pairs, eq_names, _ = primal_matrices(owner, set(selected))
    zeros = [name[1] for name in eq_names]
    zero_index = {v: i for i, v in enumerate(zeros)}
    cut = {
        z for z in zeros
        if any(owner[h][z] == endpoint for h in selected)
    }
    alpha = np.asarray([int(z in cut) for z in zeros])
    edge_demand = np.asarray([
        alpha[zero_index[v]] + alpha[zero_index[w]] for v, w in pairs
    ])
    result = linprog(
        bub, A_ub=-aub.T, b_ub=-edge_demand,
        bounds=(0, None), method="highs",
    )
    if not result.success:
        return None
    demand = int(alpha @ beq)
    capacity = float(result.fun)
    return demand - capacity, demand, capacity, int(np.sum(result.x > 1e-8))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=16)
    parser.add_argument("--codes", default="0,1")
    parser.add_argument("--profile", choices=("any", "000", "001"), default="any")
    parser.add_argument("--require", action="store_true", help="fail if a sample has no deficient endpoint")
    args = parser.parse_args()
    selected = tuple(int(value) for value in args.codes.split(","))
    if len(selected) != 2 or len(set(selected)) != 2:
        parser.error("--codes must name two distinct code indices")

    solver, variables = build_solver()
    matching_edges = (
        variables[0][PAIR01] == PAIR02,
        variables[1][PAIR01] == PAIR12,
        variables[2][PAIR02] == PAIR12,
    )
    if args.profile == "000":
        solver.add(*(z3.Not(edge) for edge in matching_edges))
    elif args.profile == "001":
        solver.add(z3.Not(matching_edges[0]), matching_edges[1], z3.Not(matching_edges[2]))
    for sample in range(args.samples):
        if solver.check() != z3.sat:
            break
        model = solver.model()
        owner = [[model.eval(variables[h][v]).as_long() for v in range(46)] for h in range(3)]
        profile = (
            int(owner[0][PAIR01] == PAIR02),
            int(owner[1][PAIR01] == PAIR12),
            int(owner[2][PAIR02] == PAIR12),
        )
        candidates = []
        for hole in holes(owner, selected):
            for endpoint in hole:
                cover = endpoint_cover(owner, selected, endpoint)
                if cover is not None and cover[0] > 1e-8:
                    candidates.append((endpoint, hole, cover))
        print(f"sample={sample} profile={profile} deficient={candidates}")
        if args.require and not candidates:
            raise RuntimeError("no deficient two-color hole endpoint cover")
        solver.add(z3.Or(*(
            variables[h][v] != owner[h][v]
            for h in range(3) for v in range(46)
        )))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
