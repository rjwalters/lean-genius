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
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from z3 import is_true, sat

from q9_b0_residual_defect_sat import N, N_TRIPLE, N_U1, build


OUTER_ONLY_RELAX = {
    "row-ledger", "residual-c4", "b0-c4", "dtb-common", "dtb-cap",
    "dtb-zero", "dtb-rows", "dtb-columns", "marked-miss",
}


def random_outer(branch: int, seed: int, timeout_seconds: int) -> dict:
    solver, data = build(
        branch, timeout_seconds * 1000, True, relax=OUTER_ONLY_RELAX
    )
    solver.set(random_seed=seed)
    if solver.check() != sat:
        raise RuntimeError("outer design generation did not return SAT")
    model = solver.model()
    return {
        "branch": branch,
        "blocks": [
            [point for point in range(N_U1)
             if is_true(model.eval(data["incidence"][row, point],
                                   model_completion=True))]
            for row in range(N)
        ],
        "k_edges": [
            list(edge) for edge, variable in data["k"].items()
            if is_true(model.eval(variable, model_completion=True))
        ],
    }


def fixed_system(payload: dict) -> dict:
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


def minimum_row_support(system: dict, big_m: float = 50) -> set[int]:
    """Find a cardinality-minimum support for the free row prices.

    A tiny continuous tie-breaker makes the returned prices/capacities small;
    the support cardinality dominates because every continuous variable is
    bounded by ``big_m`` and its total coefficient is below one.
    """
    blocks = system["blocks"]
    degree = system["degree"]
    edges = system["edges"]
    caps = system["caps"]
    cap_index = system["cap_index"]
    support_begin = 2 * N + len(caps)
    variable_count = support_begin + N
    matrix = []
    upper = []
    for u, v in edges:
        row = np.zeros(variable_count)
        row[u] = row[v] = 1
        row[N + u] = row[N + v] = -1
        for point in blocks[v]:
            row[2 * N + cap_index[u, point]] -= 1
        for point in blocks[u]:
            row[2 * N + cap_index[v, point]] -= 1
        matrix.append(row)
        upper.append(0)
    margin = np.zeros(variable_count)
    for u in range(N):
        margin[u] = -degree[u]
        margin[N + u] = degree[u]
    margin[2 * N:support_begin] = 1
    matrix.append(margin)
    upper.append(-1)
    for u in range(N):
        row = np.zeros(variable_count)
        row[u] = row[N + u] = 1
        row[support_begin + u] = -big_m
        matrix.append(row)
        upper.append(0)
    objective = np.zeros(variable_count)
    objective[:support_begin] = 1e-6
    objective[support_begin:] = 1
    integrality = np.zeros(variable_count)
    integrality[support_begin:] = 1
    variable_upper = np.full(variable_count, big_m)
    variable_upper[support_begin:] = 1
    result = milp(
        objective, integrality=integrality,
        bounds=Bounds(np.zeros(variable_count), variable_upper),
        constraints=LinearConstraint(
            np.array(matrix), np.full(len(matrix), -np.inf), np.array(upper)
        ),
        options={"time_limit": 600, "mip_rel_gap": 0},
    )
    if not result.success:
        raise RuntimeError("row-support MILP failed: " + result.message)
    return {
        u for u in range(N) if result.x[support_begin + u] > 0.5
    }


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


def unit_nondiagonal_fiber_certificate(system: dict, point: int) -> dict | None:
    """Exact unit-row-price certificate with the natural fiber price mask.

    Only outgoing point prices at the four non-diagonal roots through
    ``point`` and incoming prices at ``point`` itself are allowed.
    """
    blocks = system["blocks"]
    caps = system["caps"]
    cap_index = system["cap_index"]
    fiber = {
        row for row, block in enumerate(blocks)
        if point in block and row != point % 8
    }
    if len(fiber) != 4:
        raise RuntimeError(
            f"point {point} has non-diagonal fiber {sorted(fiber)}"
        )
    allowed = [
        index for index, (row, q) in enumerate(caps)
        if row in fiber or q == point
    ]
    position = {old: new for new, old in enumerate(allowed)}
    matrix = []
    rhs = []
    for u, v in system["edges"]:
        need = int(u in fiber) + int(v in fiber)
        if not need:
            continue
        row = np.zeros(len(allowed))
        for q in blocks[v]:
            index = cap_index[u, q]
            if index in position:
                row[position[index]] -= 1
        for q in blocks[u]:
            index = cap_index[v, q]
            if index in position:
                row[position[index]] -= 1
        matrix.append(row)
        rhs.append(-need)
    result = linprog(
        np.ones(len(allowed)), A_ub=np.array(matrix), b_ub=np.array(rhs),
        bounds=(0, None), method="highs",
    )
    if not result.success:
        return None
    prices = [
        Fraction(float(value)).limit_denominator(10**6) for value in result.x
    ]
    if any(price < 0 for price in prices):
        return None
    target = sum(system["degree"][row] for row in fiber)
    cost = sum(prices, Fraction())
    if not cost < target:
        return None
    for row, bound in zip(matrix, rhs):
        lhs = sum(
            (Fraction(int(coefficient)) * price
             for coefficient, price in zip(row, prices)), Fraction()
        )
        if lhs > bound:
            return None
    return {
        "point": point,
        "support": sorted(fiber),
        "cost": str(cost),
        "target": target,
        "point_prices": [
            (caps[allowed[i]], str(price))
            for i, price in enumerate(prices) if price
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("payload", type=Path, nargs="?")
    parser.add_argument("--branch", type=int, choices=(3, 4))
    parser.add_argument("--random-seed", type=int, default=0)
    parser.add_argument("--timeout-seconds", type=int, default=60)
    parser.add_argument("--dual", action="store_true")
    parser.add_argument("--row-support", type=int, nargs="*")
    parser.add_argument("--minimize-row-support", action="store_true")
    parser.add_argument("--scan-nondiagonal-fibers", action="store_true")
    parser.add_argument("--scan-unit-nondiagonal-fibers", action="store_true")
    args = parser.parse_args()
    if args.payload is None:
        if args.branch is None:
            parser.error("either payload or --branch is required")
        payload = random_outer(
            args.branch, args.random_seed, args.timeout_seconds
        )
    else:
        payload = json.loads(args.payload.read_text())
        if "branch" not in payload:
            if args.branch is None:
                parser.error("payload without branch requires --branch")
            payload["branch"] = args.branch
    system = fixed_system(payload)
    result = primal(system)
    print(
        f"branch={system['branch']} edges={len(system['edges'])} "
        f"caps={len(system['caps'])} primal={result.message}"
    )
    if args.scan_nondiagonal_fibers:
        successes = []
        for point in range(N_U1):
            fiber = {
                row for row, block in enumerate(system["blocks"])
                if point in block and row != point % 8
            }
            if len(fiber) != 4:
                raise RuntimeError(
                    f"point {point} has non-diagonal fiber {sorted(fiber)}"
                )
            fiber_result = dual(system, fiber)
            if fiber_result.success:
                certificate = exact_certificate(system, fiber_result)
                if certificate is not None:
                    successes.append({
                        "point": point,
                        "support": sorted(fiber),
                        "row_prices": certificate["row_prices"],
                        "margin": certificate["margin"],
                    })
        print("nondiagonal_fiber_certificates=" + json.dumps(
            successes, separators=(",", ":")
        ))
    if args.scan_unit_nondiagonal_fibers:
        certificates = [
            certificate for point in range(N_U1)
            if (certificate := unit_nondiagonal_fiber_certificate(
                system, point
            )) is not None
        ]
        print("unit_nondiagonal_fiber_certificates=" + json.dumps(
            certificates, separators=(",", ":")
        ))
    if (not args.dual and not args.minimize_row_support
            and not args.scan_nondiagonal_fibers
            and not args.scan_unit_nondiagonal_fibers):
        return
    if (args.scan_nondiagonal_fibers or args.scan_unit_nondiagonal_fibers
            ) and not (args.dual or args.minimize_row_support):
        return
    row_support = (
        minimum_row_support(system) if args.minimize_row_support
        else None if args.row_support is None else set(args.row_support)
    )
    if args.minimize_row_support:
        print("minimum_row_support=" + json.dumps(sorted(row_support)))
    dual_result = dual(
        system, row_support
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
