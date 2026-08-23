#!/usr/bin/env python3
"""Symmetric fractional residual obstruction for a fixed q=9 outer design.

The local fractional matching probes give every row its own mass vector.  An
actual residual graph has one shared symmetric edge mass instead.  This probe
tests the strictly stronger relaxation

    sum_v x_{uv} = d(u),
    sum_{v : p in B_v} x_{uv} <= 1,
    x_{uv} = x_{vu} >= 0,

on mutually trace-eligible pairs.  Infeasibility therefore needs neither
integrality nor residual C4.  ``--dual`` also searches for row prices y and
ordered point prices z satisfying

    y_u + y_v <= sum_{p in B_v} z_{u,p} + sum_{p in B_u} z_{v,p},
    sum_u d(u)y_u > sum_{u,p} z_{u,p}.

The reported exact certificate is accepted only after rationalization and a
second, purely Fraction-based verification of every inequality.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from itertools import combinations
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

from q9_b0_residual_defect_sat import N, N_TRIPLE, N_U1


def fixed_system(path: Path) -> dict:
    payload = json.loads(path.read_text())
    blocks = [set(block) for block in payload["blocks"]]
    k_edges = {tuple(sorted(edge)) for edge in payload["k_edges"]}
    holes_begin = N_TRIPLE - (2 if payload["branch"] == 3 else 4)
    degree = [6 if row >= holes_begin else 5 for row in range(N)]

    def core(row: int, point: int) -> bool:
        return any(
            source != point and tuple(sorted((source, point))) in k_edges
            for source in blocks[row]
        )

    def eligible(row: int, candidate: int) -> bool:
        return row != candidate and all(
            not core(row, point) for point in blocks[candidate]
        )

    edges = [
        edge for edge in combinations(range(N), 2)
        if eligible(*edge) and eligible(edge[1], edge[0])
    ]
    caps = []
    cap_index = {}
    for row in range(N):
        for point in range(N_U1):
            if any(
                row in edge
                and point in blocks[edge[1] if edge[0] == row else edge[0]]
                for edge in edges
            ):
                cap_index[row, point] = len(caps)
                caps.append((row, point))
    return {
        "branch": payload["branch"],
        "blocks": blocks,
        "degree": degree,
        "edges": edges,
        "caps": caps,
        "cap_index": cap_index,
    }


def primal(system: dict):
    edges = system["edges"]
    degree = system["degree"]
    caps = system["caps"]
    blocks = system["blocks"]
    matrix_eq = np.zeros((N, len(edges)))
    for column, (u, v) in enumerate(edges):
        matrix_eq[u, column] = matrix_eq[v, column] = 1
    matrix_cap = np.zeros((len(caps), len(edges)))
    for row, (u, point) in enumerate(caps):
        for column, edge in enumerate(edges):
            if u in edge:
                other = edge[1] if edge[0] == u else edge[0]
                matrix_cap[row, column] = int(point in blocks[other])
    return linprog(
        np.zeros(len(edges)), A_ub=matrix_cap, b_ub=np.ones(len(caps)),
        A_eq=matrix_eq, b_eq=np.array(degree), bounds=(0, None),
        method="highs",
    )


def dual(system: dict, row_support: set[int] | None):
    blocks = system["blocks"]
    degree = system["degree"]
    edges = system["edges"]
    caps = system["caps"]
    cap_index = system["cap_index"]
    variable_count = 2 * N + len(caps)
    matrix = []
    rhs = []
    for u, v in edges:
        row = np.zeros(variable_count)
        row[u] = row[v] = 1
        row[N + u] = row[N + v] = -1
        for point in blocks[v]:
            row[2 * N + cap_index[u, point]] -= 1
        for point in blocks[u]:
            row[2 * N + cap_index[v, point]] -= 1
        matrix.append(row)
        rhs.append(0)
    margin = np.zeros(variable_count)
    for u in range(N):
        margin[u] = -degree[u]
        margin[N + u] = degree[u]
    margin[2 * N:] = 1
    matrix.append(margin)
    rhs.append(-1)
    bounds = [
        (0, None)
        if row_support is None or u % N in row_support or u >= 2 * N
        else (0, 0)
        for u in range(variable_count)
    ]
    return linprog(
        np.ones(variable_count), A_ub=np.array(matrix), b_ub=np.array(rhs),
        bounds=bounds, method="highs",
    )


def exact_certificate(system: dict, result) -> dict | None:
    caps = system["caps"]
    cap_index = system["cap_index"]
    blocks = system["blocks"]
    degree = system["degree"]
    y = [
        Fraction(float(result.x[u] - result.x[N + u])).limit_denominator(10**6)
        for u in range(N)
    ]
    z = [
        Fraction(float(value)).limit_denominator(10**6)
        for value in result.x[2 * N:]
    ]
    slacks = [
        sum((z[cap_index[u, point]] for point in blocks[v]), Fraction())
        + sum((z[cap_index[v, point]] for point in blocks[u]), Fraction())
        - y[u] - y[v]
        for u, v in system["edges"]
    ]
    margin = (
        sum((Fraction(degree[u]) * y[u] for u in range(N)), Fraction())
        - sum(z, Fraction())
    )
    if margin <= 0 or min(slacks) < 0 or any(value < 0 for value in z):
        return None
    return {
        "margin": str(margin),
        "minimum_edge_slack": str(min(slacks)),
        "row_prices": [(u, str(value)) for u, value in enumerate(y) if value],
        "point_prices": [
            (caps[i], str(value)) for i, value in enumerate(z) if value
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("payload", type=Path)
    parser.add_argument("--dual", action="store_true")
    parser.add_argument("--row-support", type=int, nargs="*")
    args = parser.parse_args()
    system = fixed_system(args.payload)
    result = primal(system)
    print(
        f"branch={system['branch']} edges={len(system['edges'])} "
        f"caps={len(system['caps'])} primal={result.message}"
    )
    if not args.dual:
        return
    dual_result = dual(
        system, None if args.row_support is None else set(args.row_support)
    )
    print(f"dual={dual_result.message}")
    if not dual_result.success:
        return
    certificate = exact_certificate(system, dual_result)
    if certificate is None:
        raise SystemExit("floating dual did not survive exact rational audit")
    print(json.dumps(certificate, indent=2))


if __name__ == "__main__":
    main()
