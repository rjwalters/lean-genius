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


def partial_primal(system: dict, selected_rows: set[int]):
    """Global symmetric packing with degree equations only at selected rows."""
    edges = system["edges"]
    caps = system["caps"]
    blocks = system["blocks"]
    ordered_rows = sorted(selected_rows)
    matrix_eq = np.zeros((len(ordered_rows), len(edges)))
    for row_index, selected in enumerate(ordered_rows):
        for column, edge in enumerate(edges):
            matrix_eq[row_index, column] = int(selected in edge)
    matrix_cap = np.zeros((len(caps), len(edges)))
    for row, (u, point) in enumerate(caps):
        for column, edge in enumerate(edges):
            if u in edge:
                other = edge[1] if edge[0] == u else edge[0]
                matrix_cap[row, column] = int(point in blocks[other])
    return linprog(
        np.zeros(len(edges)), A_ub=matrix_cap, b_ub=np.ones(len(caps)),
        A_eq=matrix_eq,
        b_eq=np.array([system["degree"][row] for row in ordered_rows]),
        bounds=(0, None), method="highs",
    )


def pair_union_capacity(system: dict, first: int, second: int) -> float:
    """Maximum total mass incident to either of two named rows."""
    edges = system["edges"]
    caps = system["caps"]
    blocks = system["blocks"]
    objective = np.zeros(len(edges))
    for column, edge in enumerate(edges):
        objective[column] = -int(first in edge) - int(second in edge)
    matrix_cap = np.zeros((len(caps), len(edges)))
    for row, (u, point) in enumerate(caps):
        for column, edge in enumerate(edges):
            if u in edge:
                other = edge[1] if edge[0] == u else edge[0]
                matrix_cap[row, column] = int(point in blocks[other])
    result = linprog(
        objective, A_ub=matrix_cap, b_ub=np.ones(len(caps)),
        bounds=(0, None), method="highs",
    )
    if not result.success:
        raise RuntimeError("pair union-capacity LP failed: " + result.message)
    return -float(result.fun)


def dual(system: dict, row_support: set[int] | None,
         external_point: int | None = None):
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
    bounds = []
    for index in range(variable_count):
        if index < 2 * N:
            allowed = row_support is None or index % N in row_support
        else:
            cap_row, cap_point = caps[index - 2 * N]
            allowed = (
                external_point is None or row_support is None
                or cap_row in row_support or cap_point == external_point
            )
        bounds.append((0, None) if allowed else (0, 0))
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


def fixed_two_row_shared_point_certificate(
        system: dict, regular: int, hole: int, regular_weight: int,
        hole_weight: int) -> dict | None:
    """Minimize point prices for two fixed positive row prices.

    Point prices may be supported on either named row and, when the blocks
    meet, at their unique shared point.  The floating-point optimum only finds
    a candidate; every edge inequality and the strict objective margin are
    then checked over ``Fraction``.
    """
    blocks = system["blocks"]
    intersection = sorted(blocks[regular] & blocks[hole])
    if len(intersection) > 1:
        return None
    shared_point = intersection[0] if intersection else None
    caps = system["caps"]
    cap_index = system["cap_index"]
    allowed = [
        cap_row in (regular, hole)
        or (shared_point is not None and cap_point == shared_point)
        for cap_row, cap_point in caps
    ]
    matrix = []
    rhs = []
    constraint_edges = []
    row_price = {regular: regular_weight, hole: hole_weight}
    for u, v in system["edges"]:
        required = row_price.get(u, 0) + row_price.get(v, 0)
        if required == 0:
            continue
        row = np.zeros(len(caps))
        for point in blocks[v]:
            row[cap_index[u, point]] -= 1
        for point in blocks[u]:
            row[cap_index[v, point]] -= 1
        matrix.append(row)
        rhs.append(-required)
        constraint_edges.append((u, v, required))
    result = linprog(
        np.ones(len(caps)),
        A_ub=np.array(matrix), b_ub=np.array(rhs),
        bounds=[(0, None) if keep else (0, 0) for keep in allowed],
        method="highs",
    )
    if not result.success:
        return None
    prices = [
        Fraction(float(value)).limit_denominator(10**6)
        for value in result.x
    ]
    packing = [
        Fraction(float(-value)).limit_denominator(10**6)
        for value in result.ineqlin.marginals
    ]
    slacks = []
    for u, v in system["edges"]:
        required = Fraction(row_price.get(u, 0) + row_price.get(v, 0))
        supplied = (
            sum((prices[cap_index[u, point]] for point in blocks[v]),
                Fraction())
            + sum((prices[cap_index[v, point]] for point in blocks[u]),
                  Fraction())
        )
        slacks.append(supplied - required)
    target = (
        system["degree"][regular] * regular_weight
        + system["degree"][hole] * hole_weight
    )
    cost = sum(prices, Fraction())
    packing_value = sum(
        weight * required
        for weight, (_, _, required) in zip(packing, constraint_edges)
    )
    packing_capacities = [
        sum(
            (packing[index] * -Fraction(matrix[index][cap_index_value])
             for index in range(len(packing))),
            Fraction(),
        )
        for cap_index_value, keep in enumerate(allowed) if keep
    ]
    if (
        cost >= target or min(slacks) < 0
        or any(value < 0 for value in prices)
        or any(value < 0 for value in packing)
        or max(packing_capacities, default=Fraction()) > 1
        or packing_value != cost
    ):
        return None
    return {
        "regular": regular,
        "hole": hole,
        "block_intersection": intersection,
        "shared_point": shared_point,
        "regular_weight": regular_weight,
        "hole_weight": hole_weight,
        "cost": str(cost),
        "target": str(target),
        "margin": str(Fraction(target) - cost),
        "minimum_edge_slack": str(min(slacks)),
        "packing_value": str(packing_value),
        "packing": [
            ([u, v], str(weight), required)
            for weight, (u, v, required) in zip(packing, constraint_edges)
            if weight
        ],
        "point_prices": [
            (caps[index], str(value))
            for index, value in enumerate(prices) if value
        ],
    }


def disjoint_local_packing_pair(system: dict, regular: int, hole: int):
    """Find disjoint integral block-packings of the two demanded row sizes.

    This deliberately omits cross-edge reciprocity between the two rows, so
    infeasibility proves the stronger hypothesis consumed by
    ``false_of_no_disjointLocalGramPackingPair``.  A returned witness is
    rechecked combinatorially rather than trusted to floating-point MILP.
    """
    edge_set = set(system["edges"])
    regular_neighbors = {
        v for edge in edge_set if regular in edge
        for v in edge if v != regular
    }
    hole_neighbors = {
        v for edge in edge_set if hole in edge
        for v in edge if v != hole
    }
    variable_count = 2 * N
    matrix = []
    lower = []
    upper = []
    for offset, target in (
        (0, system["degree"][regular]),
        (N, system["degree"][hole]),
    ):
        row = np.zeros(variable_count)
        row[offset:offset + N] = 1
        matrix.append(row)
        lower.append(target)
        upper.append(target)
        for point in range(N_U1):
            row = np.zeros(variable_count)
            for v in range(N):
                if point in system["blocks"][v]:
                    row[offset + v] = 1
            matrix.append(row)
            lower.append(-np.inf)
            upper.append(1)
    for v in range(N):
        row = np.zeros(variable_count)
        row[v] = row[N + v] = 1
        matrix.append(row)
        lower.append(-np.inf)
        upper.append(1)
    variable_upper = np.array(
        [int(v in regular_neighbors) for v in range(N)]
        + [int(v in hole_neighbors) for v in range(N)]
    )
    result = milp(
        np.zeros(variable_count), integrality=np.ones(variable_count),
        bounds=Bounds(np.zeros(variable_count), variable_upper),
        constraints=LinearConstraint(
            np.array(matrix), np.array(lower), np.array(upper)
        ),
    )
    if result.status == 2:
        return None
    if not result.success:
        raise RuntimeError("joint local-packing MILP failed: " + result.message)
    first = {v for v in range(N) if result.x[v] > 0.5}
    second = {v for v in range(N) if result.x[N + v] > 0.5}
    valid = (
        len(first) == system["degree"][regular]
        and len(second) == system["degree"][hole]
        and first.isdisjoint(second)
        and first <= regular_neighbors and second <= hole_neighbors
        and all(
            sum(point in system["blocks"][v] for v in selected) <= 1
            for selected in (first, second) for point in range(N_U1)
        )
    )
    if not valid:
        raise RuntimeError("joint local-packing witness failed exact audit")
    return {"regular_packing": sorted(first), "hole_packing": sorted(second)}


def unit_nondiagonal_fiber_optimum(
        system: dict, point: int, include_diagonal: bool = False
        ) -> dict | None:
    """Exact unit-row-price optimum with the natural fiber price mask.

    Only outgoing point prices at the four non-diagonal roots through
    ``point`` and incoming prices at ``point`` itself are allowed.
    """
    blocks = system["blocks"]
    caps = system["caps"]
    cap_index = system["cap_index"]
    fiber = {
        row for row, block in enumerate(blocks)
        if point in block and (include_diagonal or row != point % 8)
    }
    expected_size = 5 if include_diagonal else 4
    if len(fiber) != expected_size:
        raise RuntimeError(
            f"point {point} has unexpected fiber {sorted(fiber)}"
        )
    allowed = [
        index for index, (row, q) in enumerate(caps)
        if row in fiber or q == point
    ]
    position = {old: new for new, old in enumerate(allowed)}
    matrix = []
    rhs = []
    constraint_edges = []
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
        constraint_edges.append((u, v))
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
    for row, bound in zip(matrix, rhs):
        lhs = sum(
            (Fraction(int(coefficient)) * price
             for coefficient, price in zip(row, prices)), Fraction()
        )
        if lhs > bound:
            return None
    dual = [
        Fraction(float(-value)).limit_denominator(10**6)
        for value in result.ineqlin.marginals
    ]
    if any(value < 0 for value in dual):
        return None
    for column in range(len(allowed)):
        usage = sum(
            (-Fraction(int(matrix[row][column]))) * dual[row]
            for row in range(len(matrix))
        )
        if usage > 1:
            return None
    dual_lower_bound = sum(
        (-Fraction(bound)) * value for bound, value in zip(rhs, dual)
    )
    strict = cost < target
    nonstrict = target <= dual_lower_bound
    if not strict and not nonstrict:
        return None
    return {
        "point": point,
        "support": sorted(fiber),
        "cost": str(cost),
        "target": target,
        "dual_lower_bound": str(dual_lower_bound),
        "strict": strict,
        "nonstrict": nonstrict,
        "point_prices": [
            (caps[allowed[i]], str(price))
            for i, price in enumerate(prices) if price
        ],
        # Kept private because the ordinary certificate JSON should remain
        # compact.  The branch-four descent audit consumes these exact edge
        # weights to test proposed packing-to-load identities.
        "_dual_edges": list(zip(constraint_edges, dual)),
    }


def unit_row_cover_optimum(system: dict, row: int) -> dict | None:
    """Exact fractional point-cover optimum for one row's eligible neighbors."""
    blocks = system["blocks"]
    neighbors = [
        v if u == row else u for u, v in system["edges"] if row in (u, v)
    ]
    matrix = np.array([
        [-int(point in blocks[v]) for point in range(N_U1)]
        for v in neighbors
    ], dtype=float)
    result = linprog(
        np.ones(N_U1), A_ub=matrix,
        b_ub=-np.ones(len(neighbors)), bounds=(0, None), method="highs",
    )
    if not result.success:
        return None
    cover = [
        Fraction(float(value)).limit_denominator(10**6)
        for value in result.x
    ]
    if any(value < 0 for value in cover):
        return None
    if any(
        sum((cover[point] for point in blocks[v]), Fraction()) < 1
        for v in neighbors
    ):
        return None
    packing = [
        Fraction(float(-value)).limit_denominator(10**6)
        for value in result.ineqlin.marginals
    ]
    if any(value < 0 for value in packing):
        return None
    if any(
        sum((packing[i] for i, v in enumerate(neighbors)
             if point in blocks[v]), Fraction()) > 1
        for point in range(N_U1)
    ):
        return None
    cost = sum(cover, Fraction())
    dual_lower_bound = sum(packing, Fraction())
    if dual_lower_bound != cost:
        return None
    return {
        "row": row,
        "block": sorted(blocks[row]),
        "degree": system["degree"][row],
        "cost": str(cost),
        "dual_lower_bound": str(dual_lower_bound),
        "strict": cost < system["degree"][row],
        "cover": [
            (point, str(value)) for point, value in enumerate(cover) if value
        ],
    }


def forced_local_packing_neighbors(system: dict, row: int) -> dict:
    """Enumerate demanded integral local packings and intersect their rows."""
    blocks = system["blocks"]
    neighbors = [
        v if u == row else u
        for u, v in system["edges"] if row in (u, v)
    ]
    forced = set(neighbors)
    possible = set()
    packing_count = 0
    for packing in combinations(neighbors, system["degree"][row]):
        if not all(
            blocks[u].isdisjoint(blocks[v])
            for u, v in combinations(packing, 2)
        ):
            continue
        packing_count += 1
        forced.intersection_update(packing)
        possible.update(packing)
    return {
        "packing_count": packing_count,
        "forced_neighbors": sorted(forced) if packing_count else [],
        "possible_neighbors": sorted(possible),
    }


def unit_nondiagonal_fiber_certificate(
        system: dict, point: int, include_diagonal: bool = False
        ) -> dict | None:
    """Return the exact optimum only when it is a strict certificate."""
    optimum = unit_nondiagonal_fiber_optimum(
        system, point, include_diagonal=include_diagonal
    )
    return optimum if optimum is not None and optimum["strict"] else None


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
    parser.add_argument("--scan-unit-full-fibers", action="store_true")
    parser.add_argument(
        "--scan-min-load-global-special-fibers", action="store_true",
        help=("branch 4: restrict unit full-fiber certificates to global "
              "special points minimizing the exact candidate load "
              "sum_{u in F_p} deg_H(u)"),
    )
    parser.add_argument(
        "--audit-global-special-load-descent", action="store_true",
        help=("branch 4: rationally certify strictness or non-strictness "
              "at every global-special full fiber and test whether each "
              "non-strict point has a strictly "
              "lower-load global-special competitor"),
    )
    parser.add_argument(
        "--scan-exceptional-two-row-supports", action="store_true",
        help=("scan every support {exceptional row, other row} for an exact "
              "symmetric row/point-price obstruction"),
    )
    parser.add_argument(
        "--scan-fixed-exceptional-two-row-templates", action="store_true",
        help=("branch 4: test the fixed (regular,hole)=(1,2) row-price "
              "template on every regular/exceptional pair, with prices "
              "restricted to the two rows and, when present, their unique "
              "shared point"),
    )
    parser.add_argument(
        "--scan-disjoint-exceptional-regular-packings", action="store_true",
        help=("branch 4: test every incident regular/exceptional pair for "
              "disjoint integral local block-packings of sizes five and six"),
    )
    parser.add_argument(
        "--audit-local-or-two-row-price", action="store_true",
        help=("audit the honest branch-4 (13av) disjunction: a sound local "
              "packing deficit/shared-block forced collision, or an exact "
              "global price certificate with row support at most two"),
    )
    parser.add_argument(
        "--scan-exceptional-three-row-supports", action="store_true",
        help=("branch 3: scan supports with one exceptional row and two "
              "regular triple rows"),
    )
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
    if args.scan_unit_full_fibers:
        certificates = [
            certificate for point in range(N_U1)
            if (certificate := unit_nondiagonal_fiber_certificate(
                system, point, include_diagonal=True
            )) is not None
        ]
        print("unit_full_fiber_certificates=" + json.dumps(
            certificates, separators=(",", ":")
        ))
    if args.scan_min_load_global_special_fibers:
        if system["branch"] != 4:
            parser.error("--scan-min-load-global-special-fibers requires branch 4")
        punctured_classes = (range(8, 15), range(15, 22))
        special = {
            point: sum(
                not any(point in system["blocks"][row] for row in rows)
                for rows in punctured_classes
            )
            for point in range(N_U1)
        }
        special_points = [point for point, count in special.items() if count]
        if sum(special.values()) != 6:
            raise RuntimeError(
                "branch-4 puncture mass is not six: "
                f"{sorted(special.items())}"
            )
        candidate_degree = [0] * N
        for u, v in system["edges"]:
            candidate_degree[u] += 1
            candidate_degree[v] += 1
        load = {
            point: sum(
                candidate_degree[row]
                for row, block in enumerate(system["blocks"])
                if point in block
            )
            for point in special_points
        }
        minimum_load = min(load.values())
        candidates = [
            point for point in special_points if load[point] == minimum_load
        ]
        certificates = [
            certificate for point in candidates
            if (certificate := unit_nondiagonal_fiber_certificate(
                system, point, include_diagonal=True
            )) is not None
        ]
        print("min_load_global_special_selector=" + json.dumps({
            "special_mass": sum(special.values()),
            "minimum_load": minimum_load,
            "candidates": [
                {"point": point, "special": special[point]}
                for point in candidates
            ],
            "certificates": certificates,
            "strict": bool(certificates),
        }, separators=(",", ":")))
    if args.audit_global_special_load_descent:
        if system["branch"] != 4:
            parser.error("--audit-global-special-load-descent requires branch 4")
        punctured_classes = (range(8, 15), range(15, 22))
        special = {
            point: sum(
                not any(point in system["blocks"][row] for row in rows)
                for rows in punctured_classes
            )
            for point in range(N_U1)
        }
        special_points = [point for point, count in special.items() if count]
        candidate_degree = [0] * N
        for u, v in system["edges"]:
            candidate_degree[u] += 1
            candidate_degree[v] += 1
        load = {
            point: sum(
                candidate_degree[row]
                for row, block in enumerate(system["blocks"])
                if point in block
            )
            for point in special_points
        }
        records = []
        valid = True
        for point in special_points:
            optimum = unit_nondiagonal_fiber_optimum(
                system, point, include_diagonal=True
            )
            if optimum is None:
                raise RuntimeError(f"could not verify fiber optimum at {point}")
            lower = sorted(
                q for q in special_points if load[q] < load[point]
            )
            equal = sorted(
                q for q in special_points
                if q != point and load[q] == load[point]
            )
            dual_by_edge = dict(optimum["_dual_edges"])
            residual_edges = [
                (edge, Fraction(1) - dual_by_edge.get(edge, Fraction()))
                for edge in system["edges"]
                if Fraction(1) - dual_by_edge.get(edge, Fraction()) > 0
            ]
            residual_not_landing = [
                [*edge, str(weight)] for edge, weight in residual_edges
                if not any(
                    q in system["blocks"][edge[0]]
                    or q in system["blocks"][edge[1]]
                    for q in special_points
                )
            ]
            maximum_dual_weight = max(
                (weight for _, weight in optimum["_dual_edges"]),
                default=Fraction(),
            )
            valid &= optimum["strict"] or bool(lower)
            records.append({
                "point": point,
                "special": special[point],
                "load": load[point],
                "cost": optimum["cost"],
                "dual_lower_bound": optimum["dual_lower_bound"],
                "target": optimum["target"],
                "strict": optimum["strict"],
                "nonstrict": optimum["nonstrict"],
                "lower_load_special_points": lower,
                "equal_load_special_points": equal,
                "maximum_dual_edge_weight": str(maximum_dual_weight),
                "dual_weights_at_most_one": maximum_dual_weight <= 1,
                "residual_edge_count": len(residual_edges),
                "residual_not_landing_count": len(residual_not_landing),
                "first_residual_edge_not_landing_on_special_fiber":
                    residual_not_landing[0] if residual_not_landing else None,
            })
        minimum_special_load = min(load.values())
        minimum_special_points = sorted(
            point for point in special_points
            if load[point] == minimum_special_load
        )
        one_row_certificates = []
        for row in range(N):
            certificate = unit_row_cover_optimum(system, row)
            if certificate is not None and certificate["strict"]:
                one_row_certificates.append(certificate)
        bad_minimum_points = [
            record["point"] for record in records
            if record["load"] == minimum_special_load
            and not record["strict"]
        ]
        localized_bad_minimum_points = {
            point: [
                certificate["row"] for certificate in one_row_certificates
                if point in system["blocks"][certificate["row"]]
            ]
            for point in bad_minimum_points
        }
        print("global_special_load_descent=" + json.dumps({
            "valid": valid,
            "one_row_alternative_valid": bool(one_row_certificates),
            "all_rows_fractionally_feasible": not one_row_certificates,
            "combined_valid": valid or bool(one_row_certificates),
            "localized_minimum_alternative_valid": all(
                localized_bad_minimum_points[point]
                for point in bad_minimum_points
            ),
            "bad_minimum_points_with_fiber_one_row":
                localized_bad_minimum_points,
            "one_row_certificates": one_row_certificates,
            "minimum_special_load": minimum_special_load,
            "minimum_special_points": minimum_special_points,
            "minimum_load_tie": len(minimum_special_points) > 1,
            "all_minimum_points_strict": all(
                record["strict"] for record in records
                if record["load"] == minimum_special_load
            ),
            "records": records,
        }, separators=(",", ":")))
    if args.scan_exceptional_two_row_supports:
        holes_begin = N_TRIPLE - (2 if system["branch"] == 3 else 4)
        holes = range(holes_begin, N_TRIPLE)
        punctured_classes = (
            (range(8, 15), range(15, 22))
            if system["branch"] == 4 else ()
        )
        special_count = {
            point: sum(
                not any(point in system["blocks"][row] for row in rows)
                for rows in punctured_classes
            )
            for point in range(N_U1)
        }
        edge_set = set(system["edges"])
        certificates = []
        for hole in holes:
            for other in range(N):
                if other == hole:
                    continue
                result = dual(system, {hole, other})
                if not result.success:
                    continue
                certificate = exact_certificate(system, result)
                if certificate is None:
                    continue
                pair = tuple(sorted((hole, other)))
                block_intersection = sorted(
                    system["blocks"][hole] & system["blocks"][other]
                )
                external_point_prices = [
                    (cap, value) for cap, value in certificate["point_prices"]
                    if cap[0] not in (hole, other)
                ]
                collision_certificate = None
                if other < holes_begin and len(block_intersection) == 1:
                    collision_result = dual(
                        system, {hole, other},
                        external_point=block_intersection[0],
                    )
                    if collision_result.success:
                        collision_certificate = exact_certificate(
                            system, collision_result
                        )
                certificates.append({
                    "hole": hole,
                    "other": other,
                    "other_kind": (
                        "regular-triple" if other < holes_begin
                        else "exceptional" if other < N_TRIPLE
                        else "pair"
                    ),
                    "block_intersection": block_intersection,
                    "shared_point_special": (
                        special_count[block_intersection[0]]
                        if len(block_intersection) == 1 else 0
                    ),
                    "mutually_eligible_pair": pair in edge_set,
                    "margin": certificate["margin"],
                    "row_prices": certificate["row_prices"],
                    "point_price_count": len(certificate["point_prices"]),
                    "external_point_prices": external_point_prices,
                    "shared_point_collision_normal_form": (
                        bool(block_intersection)
                        and bool(external_point_prices)
                        and all(cap[1] in block_intersection
                                for cap, _ in external_point_prices)
                    ),
                    "has_shared_point_collision_certificate":
                        collision_certificate is not None,
                    "shared_point_collision_row_prices": (
                        collision_certificate["row_prices"]
                        if collision_certificate is not None else []
                    ),
                    "shared_point_collision_point_price_count": (
                        len(collision_certificate["point_prices"])
                        if collision_certificate is not None else 0
                    ),
                })
        regular_certificates = [
            certificate for certificate in certificates
            if certificate["other_kind"] == "regular-triple"
        ]
        local = {
            row: forced_local_packing_neighbors(system, row)
            for row in range(N)
        }
        forced_collision_pairs = []
        for hole in holes:
            for regular in range(holes_begin):
                intersection = sorted(
                    system["blocks"][hole] & system["blocks"][regular]
                )
                common_forced = sorted(
                    set(local[hole]["forced_neighbors"])
                    & set(local[regular]["forced_neighbors"])
                )
                if intersection and common_forced:
                    forced_collision_pairs.append({
                        "hole": hole,
                        "regular": regular,
                        "block_intersection": intersection,
                        "common_forced_neighbors": common_forced,
                        "hole_packing_count": local[hole]["packing_count"],
                        "regular_packing_count":
                            local[regular]["packing_count"],
                    })
        print("exceptional_two_row_supports=" + json.dumps({
            "count": len(certificates),
            "regular_triple_count": len(regular_certificates),
            "exists_exceptional_regular": bool(regular_certificates),
            "exists_intersecting_exceptional_regular": any(
                certificate["block_intersection"]
                for certificate in regular_certificates
            ),
            "exists_regular_shared_point_collision_normal_form": any(
                certificate["has_shared_point_collision_certificate"]
                for certificate in regular_certificates
            ),
            "exists_special_shared_point_collision": any(
                certificate["has_shared_point_collision_certificate"]
                and certificate["shared_point_special"] > 0
                for certificate in regular_certificates
            ),
            "exists_exceptional_regular_forced_collision":
                bool(forced_collision_pairs),
            "forced_collision_pairs": forced_collision_pairs,
            "certificates": certificates,
        }, separators=(",", ":")))
    if args.scan_fixed_exceptional_two_row_templates:
        if system["branch"] != 4:
            parser.error(
                "--scan-fixed-exceptional-two-row-templates requires branch 4"
            )
        templates = [(1, 2)]
        holes_begin = N_TRIPLE - 4
        certificates = []
        for regular in range(holes_begin):
            for hole in range(holes_begin, N_TRIPLE):
                for regular_weight, hole_weight in templates:
                    certificate = fixed_two_row_shared_point_certificate(
                        system, regular, hole, regular_weight, hole_weight
                    )
                    if certificate is not None:
                        certificate["template"] = [
                            regular_weight, hole_weight
                        ]
                        certificates.append(certificate)
        template_counts = {
            f"{regular_weight}:{hole_weight}": sum(
                certificate["template"] == [regular_weight, hole_weight]
                for certificate in certificates
            )
            for regular_weight, hole_weight in templates
        }
        local = {
            row: forced_local_packing_neighbors(system, row)
            for row in range(N)
        }
        for certificate in certificates:
            regular = certificate["regular"]
            hole = certificate["hole"]
            certificate["reciprocity_mismatch"] = (
                (hole in local[regular]["forced_neighbors"]
                 and regular not in local[hole]["possible_neighbors"])
                or
                (regular in local[hole]["forced_neighbors"]
                 and hole not in local[regular]["possible_neighbors"])
            )
        global_reciprocity_pairs = [
            [u, w]
            for u in range(N) for w in local[u]["forced_neighbors"]
            if local[u]["packing_count"]
            and local[w]["packing_count"]
            and u not in local[w]["possible_neighbors"]
        ]
        print("fixed_exceptional_two_row_templates=" + json.dumps({
            "templates": templates,
            "certificate_count": len(certificates),
            "intersecting_certificate_count": sum(
                bool(certificate["block_intersection"])
                for certificate in certificates
            ),
            "disjoint_certificate_count": sum(
                not certificate["block_intersection"]
                for certificate in certificates
            ),
            "reciprocity_certificate_count": sum(
                certificate["reciprocity_mismatch"]
                for certificate in certificates
            ),
            "global_reciprocity_pairs": global_reciprocity_pairs,
            "exists_incident_or_global_reciprocity": (
                any(certificate["block_intersection"]
                    for certificate in certificates)
                or bool(global_reciprocity_pairs)
            ),
            "exists_certificate": bool(certificates),
            "template_counts": template_counts,
            "certificates": certificates,
        }, separators=(",", ":")))
    if args.scan_disjoint_exceptional_regular_packings:
        if system["branch"] != 4:
            parser.error(
                "--scan-disjoint-exceptional-regular-packings requires branch 4"
            )
        holes_begin = N_TRIPLE - 4
        packing_counts = {
            row: forced_local_packing_neighbors(system, row)["packing_count"]
            for row in range(N_TRIPLE)
        }
        records = []
        for regular in range(holes_begin):
            for hole in range(holes_begin, N_TRIPLE):
                intersection = sorted(
                    system["blocks"][regular] & system["blocks"][hole]
                )
                if len(intersection) != 1:
                    continue
                witness = disjoint_local_packing_pair(system, regular, hole)
                records.append({
                    "regular": regular,
                    "hole": hole,
                    "shared_point": intersection[0],
                    "regular_packing_count": packing_counts[regular],
                    "hole_packing_count": packing_counts[hole],
                    "has_disjoint_pair": witness is not None,
                    "witness": witness,
                })
        obstructed = [record for record in records
                      if not record["has_disjoint_pair"]]
        print("disjoint_exceptional_regular_packings=" + json.dumps({
            "incident_pair_count": len(records),
            "obstructed_pair_count": len(obstructed),
            "minimum_obstructed_hole_packing_count": (
                min(record["hole_packing_count"] for record in obstructed)
                if obstructed else None
            ),
            "exists_obstructed_pair": bool(obstructed),
            "obstructed_pairs": [
                [record["regular"], record["hole"]]
                for record in obstructed
            ],
            "records": records,
        }, separators=(",", ":")))
    if args.audit_local_or_two_row_price:
        local = {
            row: forced_local_packing_neighbors(system, row)
            for row in range(N)
        }
        deficit_rows = [
            row for row in range(N) if local[row]["packing_count"] == 0
        ]
        forced_collisions = []
        disjoint_pair_obstructions = []
        for u, v in combinations(range(N), 2):
            intersection = sorted(system["blocks"][u] & system["blocks"][v])
            if not intersection:
                continue
            common = sorted(
                set(local[u]["forced_neighbors"])
                & set(local[v]["forced_neighbors"])
            )
            if common:
                forced_collisions.append({
                    "first": u,
                    "second": v,
                    "block_intersection": intersection,
                    "common_forced_neighbors": common,
                    "first_packing_count": local[u]["packing_count"],
                    "second_packing_count": local[v]["packing_count"],
                })
            if (
                local[u]["packing_count"]
                and local[v]["packing_count"]
                and disjoint_local_packing_pair(system, u, v) is None
            ):
                disjoint_pair_obstructions.append({
                    "first": u,
                    "second": v,
                    "block_intersection": intersection,
                    "first_packing_count": local[u]["packing_count"],
                    "second_packing_count": local[v]["packing_count"],
                })
        has_local_obstruction = bool(deficit_rows or forced_collisions)
        reciprocity_obstructions = [
            [u, w]
            for u in range(N) for w in local[u]["forced_neighbors"]
            if local[u]["packing_count"]
            and local[w]["packing_count"]
            and u not in local[w]["possible_neighbors"]
        ]
        rigid_rows = [
            u for u in range(N) if 0 < local[u]["packing_count"] <= 2
        ]
        rigid_conflict_edges = [
            [u, v]
            for index, u in enumerate(rigid_rows)
            for v in rigid_rows[index + 1:]
            if system["blocks"][u] & system["blocks"][v]
        ]
        rigid_parent = {u: u for u in rigid_rows}

        def rigid_find(u: int) -> int:
            while rigid_parent[u] != u:
                rigid_parent[u] = rigid_parent[rigid_parent[u]]
                u = rigid_parent[u]
            return u

        rigid_conflict_forest = True
        for u, v in rigid_conflict_edges:
            first, second = rigid_find(u), rigid_find(v)
            if first == second:
                rigid_conflict_forest = False
                break
            rigid_parent[first] = second
        has_strengthened_local_obstruction = bool(
            has_local_obstruction or disjoint_pair_obstructions
            or reciprocity_obstructions
        )
        row_support = None
        price_certificate = None
        equal_row_price_certificates = []
        infeasible_two_row_projections = []
        infeasible_pair_packing_counts = []
        selected_partial_primal_feasible = None
        proper_subset_partial_primals_feasible = None
        if not has_local_obstruction and not result.success:
            infeasible_two_row_projections = [
                [u, v] for u, v in combinations(range(N), 2)
                if not partial_primal(system, {u, v}).success
            ]
            infeasible_pair_packing_counts = [
                {
                    "rows": [u, v],
                    "packing_counts": [
                        local[u]["packing_count"],
                        local[v]["packing_count"],
                    ],
                    "degree_sum": system["degree"][u] + system["degree"][v],
                    "union_capacity": pair_union_capacity(system, u, v),
                }
                for u, v in infeasible_two_row_projections
            ]
            row_support = sorted(minimum_row_support(system))
            selected_partial_primal_feasible = bool(
                partial_primal(system, set(row_support)).success
            )
            proper_subset_partial_primals_feasible = (
                True if len(row_support) <= 1 else
                all(partial_primal(system, {row}).success
                    for row in row_support)
            )
            if len(row_support) <= 2:
                price_result = dual(system, set(row_support))
                if price_result.success:
                    price_certificate = exact_certificate(system, price_result)
            if not has_strengthened_local_obstruction:
                equal_row_price_certificates = [
                    certificate
                    for u, v in combinations(range(N), 2)
                    if (certificate := fixed_two_row_shared_point_certificate(
                        system, u, v, 1, 1
                    )) is not None
                ]
        print("local_or_two_row_price=" + json.dumps({
            "global_fractional_packing_feasible": bool(result.success),
            "deficit_rows": deficit_rows,
            "forced_collisions": forced_collisions,
            "has_local_obstruction": has_local_obstruction,
            "disjoint_pair_obstructions": disjoint_pair_obstructions,
            "reciprocity_obstructions": reciprocity_obstructions,
            "rigid_rows": [
                [u, local[u]["packing_count"]] for u in rigid_rows
            ],
            "rigid_conflict_edges": rigid_conflict_edges,
            "rigid_conflict_forest": rigid_conflict_forest,
            "has_strengthened_local_obstruction":
                has_strengthened_local_obstruction,
            "minimum_row_support": row_support,
            "infeasible_two_row_projections":
                infeasible_two_row_projections,
            "infeasible_pair_packing_counts":
                infeasible_pair_packing_counts,
            "exists_infeasible_pair_with_at_most_two_packings": (
                None if has_local_obstruction else any(
                    min(record["packing_counts"]) <= 2
                    for record in infeasible_pair_packing_counts
                )
            ),
            "exists_non_hall_infeasible_pair": (
                None if has_local_obstruction else any(
                    record["union_capacity"] + 1e-8 >= record["degree_sum"]
                    for record in infeasible_pair_packing_counts
                )
            ),
            "all_infeasible_pairs_contain_exceptional": (
                None if has_local_obstruction else all(
                    (N_TRIPLE - 4 <= u < N_TRIPLE)
                    or (N_TRIPLE - 4 <= v < N_TRIPLE)
                    for u, v in infeasible_two_row_projections
                )
            ),
            "selected_partial_primal_feasible":
                selected_partial_primal_feasible,
            "proper_subset_partial_primals_feasible":
                proper_subset_partial_primals_feasible,
            "has_exact_two_row_price": price_certificate is not None,
            "price_certificate": price_certificate,
            "equal_row_price_certificate_count":
                len(equal_row_price_certificates),
            "equal_row_price_certificates": equal_row_price_certificates,
            "valid": has_local_obstruction or price_certificate is not None,
            "valid_strengthened": (
                has_strengthened_local_obstruction
                or price_certificate is not None
            ),
            "valid_equal_weight_strengthened": (
                has_strengthened_local_obstruction
                or bool(equal_row_price_certificates)
            ),
        }, separators=(",", ":")))
    if args.scan_exceptional_three_row_supports:
        if system["branch"] != 3:
            parser.error(
                "--scan-exceptional-three-row-supports requires branch 3")
        holes_begin = N_TRIPLE - 2
        certificates = []
        for hole in range(holes_begin, N_TRIPLE):
            for first, second in combinations(range(holes_begin), 2):
                result = dual(system, {hole, first, second})
                if not result.success:
                    continue
                certificate = exact_certificate(system, result)
                if certificate is None:
                    continue
                incident_point = None
                collision_certificate = None
                diagonal_collision_point = None
                diagonal_collision_certificate = None
                if first < 8 and 8 <= second < 16:
                    intersection = (
                        system["blocks"][hole]
                        & system["blocks"][second]
                    )
                    if len(intersection) == 1:
                        incident_point = next(iter(intersection))
                        collision_result = dual(
                            system, {hole, first, second},
                            external_point=incident_point,
                        )
                        if collision_result.success:
                            collision_certificate = exact_certificate(
                                system, collision_result
                            )
                    diagonal_intersection = (
                        system["blocks"][first]
                        & system["blocks"][second]
                    )
                    if len(diagonal_intersection) == 1:
                        diagonal_collision_point = next(iter(
                            diagonal_intersection
                        ))
                        diagonal_collision_result = dual(
                            system, {hole, first, second},
                            external_point=diagonal_collision_point,
                        )
                        if diagonal_collision_result.success:
                            diagonal_collision_certificate = exact_certificate(
                                system, diagonal_collision_result
                            )
                certificates.append({
                    "hole": hole,
                    "regular_rows": [first, second],
                    "margin": certificate["margin"],
                    "row_prices": certificate["row_prices"],
                    "point_price_count": len(certificate["point_prices"]),
                    "incident_point": incident_point,
                    "has_incident_point_collision_certificate":
                        collision_certificate is not None,
                    "incident_point_collision_certificate": (
                        None if collision_certificate is None else {
                            "margin": collision_certificate["margin"],
                            "row_prices":
                                collision_certificate["row_prices"],
                            "point_price_count": len(
                                collision_certificate["point_prices"]
                            ),
                        }
                    ),
                    "diagonal_collision_point": diagonal_collision_point,
                    "has_diagonal_collision_certificate":
                        diagonal_collision_certificate is not None,
                    "diagonal_collision_certificate": (
                        None if diagonal_collision_certificate is None else {
                            "margin":
                                diagonal_collision_certificate["margin"],
                            "row_prices":
                                diagonal_collision_certificate["row_prices"],
                            "point_price_count": len(
                                diagonal_collision_certificate["point_prices"]
                            ),
                        }
                    ),
                })
        print("exceptional_three_row_supports=" + json.dumps({
            "count": len(certificates),
            "normalized_class_pair_count": sum(
                certificate["regular_rows"][0] < 8
                and 8 <= certificate["regular_rows"][1] < 16
                for certificate in certificates
            ),
            "normalized_class_pair_certificates": [
                certificate for certificate in certificates
                if (certificate["regular_rows"][0] < 8
                    and 8 <= certificate["regular_rows"][1] < 16)
            ],
            "incident_offdiagonal_count": sum(
                certificate["regular_rows"][0] < 8
                and 8 <= certificate["regular_rows"][1] < 16
                and not system["blocks"][certificate["hole"]].isdisjoint(
                    system["blocks"][certificate["regular_rows"][1]])
                for certificate in certificates
            ),
            "incident_offdiagonal_certificates": [
                certificate for certificate in certificates
                if (certificate["regular_rows"][0] < 8
                    and 8 <= certificate["regular_rows"][1] < 16
                    and not system["blocks"][certificate["hole"]].isdisjoint(
                        system["blocks"][certificate["regular_rows"][1]]))
            ],
            "incident_point_collision_count": sum(
                certificate["has_incident_point_collision_certificate"]
                for certificate in certificates
            ),
            "incident_point_collision_certificates": [
                certificate for certificate in certificates
                if certificate["has_incident_point_collision_certificate"]
            ],
            "diagonal_collision_count": sum(
                certificate["has_diagonal_collision_certificate"]
                for certificate in certificates
            ),
            "diagonal_collision_certificates": [
                certificate for certificate in certificates
                if certificate["has_diagonal_collision_certificate"]
            ],
            "either_collision_count": sum(
                certificate["has_incident_point_collision_certificate"]
                or certificate["has_diagonal_collision_certificate"]
                for certificate in certificates
            ),
            "certificates": certificates,
        }, separators=(",", ":")))
    if (not args.dual and not args.minimize_row_support
            and not args.scan_nondiagonal_fibers
            and not args.scan_unit_nondiagonal_fibers
            and not args.scan_unit_full_fibers
            and not args.scan_min_load_global_special_fibers
            and not args.audit_global_special_load_descent
            and not args.scan_exceptional_two_row_supports
            and not args.scan_exceptional_three_row_supports):
        return
    if (args.scan_nondiagonal_fibers or args.scan_unit_nondiagonal_fibers
            or args.scan_unit_full_fibers
            or args.scan_min_load_global_special_fibers
            or args.audit_global_special_load_descent
            or args.scan_exceptional_two_row_supports
            or args.scan_exceptional_three_row_supports
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
