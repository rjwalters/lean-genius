#!/usr/bin/env python3
"""Extract a Farkas certificate for the symmetric two-color LP obstruction."""

from __future__ import annotations

import argparse

import numpy as np
import z3
from scipy.optimize import linprog

from probe_order49_three_open_code_holonomy import CODES, build_solver, degree, support


def primal_matrices(owner_values: list[list[int]], selected_codes: set[int]):
    zeros = [v for v in range(46) if support(v) == 0]
    pairs = [(v, w) for i, v in enumerate(zeros) for w in zeros[i + 1 :]]
    pair_index = {pair: i for i, pair in enumerate(pairs)}

    def fixed_edge(v: int, w: int) -> bool:
        if v == w:
            return False
        endpoint = v if support(v) else w
        other = w if endpoint == v else v
        if not support(endpoint):
            raise ValueError("zero-zero edge is variable")
        return any(
            endpoint in code and owner_values[h][other] == endpoint
            for h, code in enumerate(CODES)
        )

    aeq, beq, eq_names = [], [], []
    for v in zeros:
        row = np.zeros(len(pairs))
        for w in zeros:
            if w != v:
                row[pair_index[min(v, w), max(v, w)]] = 1
        fixed = sum(fixed_edge(v, w) for w in range(46) if support(w))
        aeq.append(row)
        beq.append(degree(v) - fixed)
        eq_names.append(("degree", v))

    aub, bub, ub_names = [], [], []
    ones = sorted({u for h in selected_codes for u in CODES[h] if support(u) == 1})
    for z in zeros:
        for u in ones:
            row = np.zeros(len(pairs))
            fixed_common = 0
            for w in range(46):
                if not fixed_edge(u, w):
                    continue
                if support(w) == 0 and w != z:
                    row[pair_index[min(z, w), max(z, w)]] += 1
                elif support(w) and fixed_edge(z, w):
                    fixed_common += 1
            aub.append(row)
            bub.append(1 - fixed_common)
            ub_names.append(("cap", z, u))
    return (
        np.asarray(aeq),
        np.asarray(beq),
        np.asarray(aub),
        np.asarray(bub),
        pairs,
        eq_names,
        ub_names,
    )


def extract_certificate(owner_values: list[list[int]], selected_codes: set[int]):
    aeq, beq, aub, bub, pairs, eq_names, ub_names = primal_matrices(
        owner_values, selected_codes
    )
    m_eq, n = aeq.shape
    m_ub = aub.shape[0]
    # Nonnegative variables are y+, y-, lambda, upper-bound, lower-bound.
    total = 2 * m_eq + m_ub + 2 * n
    coefficient_equalities = np.zeros((n, total))
    coefficient_equalities[:, :m_eq] = aeq.T
    coefficient_equalities[:, m_eq : 2 * m_eq] = -aeq.T
    coefficient_equalities[:, 2 * m_eq : 2 * m_eq + m_ub] = aub.T
    upper_offset = 2 * m_eq + m_ub
    lower_offset = upper_offset + n
    coefficient_equalities[:, upper_offset : upper_offset + n] = np.eye(n)
    coefficient_equalities[:, lower_offset : lower_offset + n] = -np.eye(n)

    rhs_row = np.zeros(total)
    rhs_row[:m_eq] = beq
    rhs_row[m_eq : 2 * m_eq] = -beq
    rhs_row[2 * m_eq : 2 * m_eq + m_ub] = bub
    rhs_row[upper_offset : upper_offset + n] = 1
    result = linprog(
        np.ones(total),
        A_ub=np.asarray([rhs_row]),
        b_ub=np.asarray([-1.0]),
        A_eq=coefficient_equalities,
        b_eq=np.zeros(n),
        bounds=(0, None),
        method="highs-ds",
    )
    if not result.success:
        raise RuntimeError(f"dual certificate LP failed: {result.message}")
    vector = result.x
    y = vector[:m_eq] - vector[m_eq : 2 * m_eq]
    lam = vector[2 * m_eq : 2 * m_eq + m_ub]
    upper = vector[upper_offset : upper_offset + n]
    lower = vector[lower_offset : lower_offset + n]
    residual = aeq.T @ y + aub.T @ lam + upper - lower
    rhs = beq @ y + bub @ lam + upper.sum()
    threshold = 1e-8
    print(f"certificate_rhs {rhs:.12g}")
    print(f"certificate_residual_max {np.abs(residual).max():.3g}")
    print(f"degree_terms {[(eq_names[i], round(y[i], 8)) for i in range(m_eq) if abs(y[i]) > threshold]}")
    print(f"cap_terms {[(ub_names[i], round(lam[i], 8)) for i in range(m_ub) if lam[i] > threshold]}")
    print(f"upper_terms {[(pairs[i], round(upper[i], 8)) for i in range(n) if upper[i] > threshold]}")
    print(f"lower_terms {[(pairs[i], round(lower[i], 8)) for i in range(n) if lower[i] > threshold]}")
    pairpoints = {0, 1, 2}
    def descriptor(v: int):
        owners = tuple(owner_values[h][v] for h in range(3))
        return {
            "v": v,
            "support": support(v),
            "owners": owners,
            "pairpoint_owners": tuple(sorted(set(owners) & pairpoints)),
        }
    selected_degree_vertices = [i for i in range(m_eq) if abs(y[i]) > threshold]
    selected_cap_vertices = sorted({
        ub_names[i][2] for i in range(m_ub) if lam[i] > threshold
    })
    print(f"degree_descriptors {[descriptor(eq_names[i][1]) for i in selected_degree_vertices]}")
    print(f"cap_owner_descriptors {[descriptor(v) for v in selected_cap_vertices]}")
    selected = sorted(selected_codes)
    groups = [
        tuple(v for v in CODES[h] if support(v) == 1) for h in selected
    ]
    realized = {
        (owner_values[selected[0]][v], owner_values[selected[1]][v])
        for v in range(46)
        if not (set(owner_values[h][v] for h in selected) & pairpoints)
    }
    holes = [(a, b) for a in groups[0] for b in groups[1] if (a, b) not in realized]
    print(f"two_color_holes {holes}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--codes", default="0,1")
    parser.add_argument("--samples", type=int, default=1)
    args = parser.parse_args()
    selected_codes = {int(value) for value in args.codes.split(",")}
    owners, variables = build_solver()
    for sample in range(args.samples):
        if owners.check() != z3.sat:
            raise RuntimeError("owner model unexpectedly unavailable")
        model = owners.model()
        values = [
            [model.eval(variables[h][v]).as_long() for v in range(46)]
            for h in range(3)
        ]
        print(f"sample {sample}")
        extract_certificate(values, selected_codes)
        owners.add(z3.Or(*(
            variables[h][v] != values[h][v]
            for h in range(3) for v in range(46)
        )))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
