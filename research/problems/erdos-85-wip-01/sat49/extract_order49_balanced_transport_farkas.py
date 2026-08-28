#!/usr/bin/env python3
"""Extract a Farkas ray for the four-family balanced transport obstruction."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction

import numpy as np
import z3
from scipy.optimize import linprog

from extract_order49_two_color_farkas import primal_matrices
from probe_order49_three_open_code_holonomy import (
    CODES, PAIR01, PAIR02, PAIR12, build_solver,
)


def transport_matrices(owner: list[list[int]]):
    _, demand, caps, capacity, pairs, degree_names, cap_names = primal_matrices(
        owner, {0, 1}
    )
    zeros = [name[1] for name in degree_names]
    arcs = [(v, w) for v in zeros for w in zeros if v != w]
    arc_index = {arc: i for i, arc in enumerate(arcs)}
    pair_index = {pair: i for i, pair in enumerate(pairs)}
    equalities, equality_names = [], []
    for side, incoming in (("row", False), ("column", True)):
        for z in zeros:
            vector = np.zeros(len(arcs))
            for w in zeros:
                if w != z:
                    vector[arc_index[(w, z) if incoming else (z, w)]] = 1
            equalities.append(vector)
            equality_names.append((side, z))
    inequalities, inequality_names, rhs = [], [], []
    for transpose, side in ((False, "row"), (True, "column")):
        for i, (_, z, u) in enumerate(cap_names):
            vector = np.zeros(len(arcs))
            for w in zeros:
                if w != z:
                    coefficient = caps[i, pair_index[(min(z, w), max(z, w))]]
                    vector[arc_index[(w, z) if transpose else (z, w)]] = coefficient
            inequalities.append(vector)
            inequality_names.append((side, z, u))
            rhs.append(capacity[i])
    return (
        np.asarray(equalities), np.concatenate((demand, demand)),
        np.asarray(inequalities), np.asarray(rhs), equality_names,
        inequality_names, zeros,
    )


def extract(owner: list[list[int]], degree_side: str = "both"):
    eq, eq_rhs, ub, ub_rhs, eq_names, ub_names, _ = transport_matrices(owner)
    if degree_side != "both":
        selected = [i for i, (side, _) in enumerate(eq_names) if side == degree_side]
        eq = eq[selected]
        eq_rhs = eq_rhs[selected]
        eq_names = [eq_names[i] for i in selected]
    equality_count = len(eq)
    columns = np.concatenate((eq.T, -eq.T, ub.T), axis=1)
    rhs = np.concatenate((eq_rhs, -eq_rhs, ub_rhs))
    result = linprog(
        np.ones(columns.shape[1]), A_ub=-columns,
        b_ub=np.zeros(columns.shape[0]), A_eq=rhs[None, :],
        b_eq=np.asarray([-1.0]), bounds=(0, None), method="highs",
    )
    if not result.success:
        raise RuntimeError(result.message)
    y = result.x[:equality_count] - result.x[equality_count:2 * equality_count]
    lam = result.x[2 * equality_count:]
    residual = eq.T @ y + ub.T @ lam
    print(f"rhs={eq_rhs @ y + ub_rhs @ lam:.12g} min_residual={residual.min():.3g}")
    degree_terms = [
        (eq_names[i], Fraction(float(value)).limit_denominator(1000))
        for i, value in enumerate(y) if abs(value) > 1e-8
    ]
    cap_terms = [
        (ub_names[i], Fraction(float(value)).limit_denominator(1000), int(ub_rhs[i]))
        for i, value in enumerate(lam) if value > 1e-8
    ]
    print(f"degree_terms={degree_terms}")
    print(f"cap_terms={cap_terms}")
    grouped = Counter()
    owner_coefficients = defaultdict(Counter)
    for (side, z, u), coefficient, capacity in cap_terms:
        color = next(h for h in (0, 1) if u in CODES[h])
        grouped[side, color, coefficient, capacity] += 1
        owner_coefficients[side, color][tuple(owner[h][z] for h in range(3)), coefficient, capacity] += 1
    print(f"cap_grouped={sorted(grouped.items())}")
    print(f"degree_owner_descriptors={[(side, z, tuple(owner[h][z] for h in range(3)), c) for (side, z), c in degree_terms]}")
    print(f"cap_owner_groups={dict(owner_coefficients)}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=("000", "001"), required=True)
    parser.add_argument("--samples", type=int, default=1)
    parser.add_argument("--degree-side", choices=("both", "row", "column"), default="both")
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
        owner = [[model.eval(variables[h][v]).as_long() for v in range(46)] for h in range(3)]
        print(f"sample={sample}")
        extract(owner, args.degree_side)
        solver.add(z3.Or(*(
            variables[h][v] != owner[h][v]
            for h in range(3) for v in range(46)
        )))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
