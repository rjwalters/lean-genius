#!/usr/bin/env python3
"""Exact joint-price probe on the two branch-3 exceptional covers.

Each exceptional row has a 15-point residual block cover.  Their intersection
has at least six points, and every such point is doubly saturated by the two
hole rows.  For distinct overlap points ``p,q`` this script puts joint row
price ``1_{F_p} + 1_{F_q}`` and searches the reduced integer point-price mask:
outgoing prices at rows in either fiber, plus incoming prices at ``p`` or
``q``.  A scaled cost below ``54*k`` is consumed directly by the generic
symmetric row/point-price theorem; it need not split into a strict single
fiber.

The MILP result is reconstructed and checked with exact integer arithmetic.
Generated models include both exact exceptional six-packs, hole reciprocity,
and the C4-free full-pack overlap cap.  This remains finite evidence, not a
uniform theorem.  ``--diagonal-rows`` and ``--all-regular-classes`` impose
the corresponding exact residual complement partitions as a retention
ladder toward global cross-row agreement.  The monolithic all-regular search
is difficult; ``--stage-all-regular-classes`` first solves the cap-only
two-class system, freezes its outer design, then restores hole reciprocity.
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

from q9_b0_residual_defect_sat import color
from q9_exceptional_hole_sixpack_sat import build
from q9_regular_class_extension_probe import freeze_outer
from q9_symmetric_point_mass_obstruction import (
    fixed_system,
    unit_nondiagonal_fiber_optimum,
)


def scaled_joint_cover(
        system: dict, p: int, q: int, scale: int, details: bool = False):
    row_price = [
        int(p in block) + int(q in block) for block in system["blocks"]
    ]
    support = {u for u, value in enumerate(row_price) if value}
    allowed = [
        index for index, (u, point) in enumerate(system["caps"])
        if u in support or point in (p, q)
    ]
    position = {old: new for new, old in enumerate(allowed)}
    matrix = []
    lower = []
    for u, v in system["edges"]:
        need = row_price[u] + row_price[v]
        if not need:
            continue
        row = np.zeros(len(allowed), dtype=int)
        for point in system["blocks"][v]:
            index = system["cap_index"][u, point]
            if index in position:
                row[position[index]] += 1
        for point in system["blocks"][u]:
            index = system["cap_index"][v, point]
            if index in position:
                row[position[index]] += 1
        matrix.append(row)
        lower.append(scale * need)
    target = sum(
        degree * price
        for degree, price in zip(system["degree"], row_price)
    )
    result = milp(
        np.ones(len(allowed)),
        integrality=np.ones(len(allowed)),
        bounds=Bounds(0, 4 * scale),
        constraints=[
            LinearConstraint(np.array(matrix), np.array(lower), np.inf),
            LinearConstraint(
                np.ones((1, len(allowed))), -np.inf, scale * target - 1
            ),
        ],
        options={"mip_rel_gap": 0, "time_limit": 60},
    )
    if result.status == 2:
        return None
    if not result.success:
        raise RuntimeError(result.message)
    prices = np.rint(result.x).astype(int)
    scaled_cost = int(prices.sum())
    slacks = np.array(matrix, dtype=int) @ prices - np.array(lower, dtype=int)
    if np.any(prices < 0) or np.any(prices > 4 * scale):
        raise RuntimeError("integer reconstruction violates price bounds")
    if int(slacks.min()) < 0 or scaled_cost >= scale * target:
        raise RuntimeError("integer reconstruction violates the joint cover")
    certificate = {
        "points": [p, q],
        "scale": scale,
        "scaled_cost": scaled_cost,
        "scaled_target": scale * target,
        "minimum_scaled_slack": int(slacks.min()),
    }
    if details:
        certificate["fiber_rows"] = {
            str(point): [u for u, block in enumerate(system["blocks"])
                         if point in block]
            for point in (p, q)
        }
        certificate["fiber_blocks"] = {
            str(u): sorted(system["blocks"][u]) for u in sorted(support)
        }
        certificate["nonzero_prices"] = [
            [*system["caps"][old], int(prices[new])]
            for new, old in enumerate(allowed) if prices[new]
        ]
        certificate["tight_edges"] = [
            [*edge, int(slack)] for edge, slack in zip(
                [edge for edge in system["edges"]
                 if row_price[edge[0]] + row_price[edge[1]]],
                slacks,
            ) if slack == 0
        ]
    return certificate


def exact_joint_optimum(system: dict, p: int, q: int) -> dict:
    """Rationally verify a continuous primal/dual optimum for diagnostics."""
    row_price = [
        int(p in block) + int(q in block) for block in system["blocks"]
    ]
    support = {u for u, value in enumerate(row_price) if value}
    allowed = [
        index for index, (u, point) in enumerate(system["caps"])
        if u in support or point in (p, q)
    ]
    position = {old: new for new, old in enumerate(allowed)}
    edges = []
    matrix = []
    needs = []
    for u, v in system["edges"]:
        need = row_price[u] + row_price[v]
        if not need:
            continue
        row = np.zeros(len(allowed), dtype=int)
        for point in system["blocks"][v]:
            index = system["cap_index"][u, point]
            if index in position:
                row[position[index]] += 1
        for point in system["blocks"][u]:
            index = system["cap_index"][v, point]
            if index in position:
                row[position[index]] += 1
        edges.append((u, v))
        matrix.append(row)
        needs.append(need)
    result = linprog(
        np.ones(len(allowed)), A_ub=-np.array(matrix),
        b_ub=-np.array(needs), bounds=(0, None), method="highs",
    )
    if not result.success:
        raise RuntimeError("joint covering LP failed: " + result.message)
    prices = [
        Fraction(float(value)).limit_denominator(10**6)
        for value in result.x
    ]
    dual = [
        Fraction(float(-value)).limit_denominator(10**6)
        for value in result.ineqlin.marginals
    ]
    primal_slacks = [
        sum((Fraction(int(a)) * value
             for a, value in zip(row, prices)), Fraction()) - need
        for row, need in zip(matrix, needs)
    ]
    dual_slacks = [
        Fraction(1) - sum(
            (Fraction(int(matrix[i][j])) * dual[i]
             for i in range(len(edges))), Fraction())
        for j in range(len(allowed))
    ]
    primal_cost = sum(prices, Fraction())
    dual_value = sum(
        (Fraction(need) * value for need, value in zip(needs, dual)),
        Fraction(),
    )
    if (min(prices) < 0 or min(dual) < 0 or min(primal_slacks) < 0
            or min(dual_slacks) < 0 or primal_cost != dual_value):
        raise RuntimeError("rational reconstruction did not certify optimum")
    return {
        "cost": str(primal_cost),
        "target": sum(
            degree * price
            for degree, price in zip(system["degree"], row_price)
        ),
        "minimum_primal_slack": str(min(primal_slacks)),
        "minimum_dual_slack": str(min(dual_slacks)),
        "point_prices": [
            [*system["caps"][old], str(prices[new])]
            for new, old in enumerate(allowed) if prices[new]
        ],
        "dual_edges": [
            [*edge, str(value)]
            for edge, value in zip(edges, dual) if value
        ],
    }


def one_model(
        timeout_ms: int, random_seed: int, max_scale: int,
        details: bool = False, genuine_only: bool = False,
        diagonal_rows: bool = False, all_regular_classes: bool = False,
        regular_class_indices: tuple[int, ...] | None = None,
        stage_all_regular_classes: bool = False):
    if stage_all_regular_classes:
        source_solver, source_data = build(
            3, timeout_ms, True, all_regular_classes=True,
            hole_full_pack_overlap_cap=True,
        )
        source_solver.set(random_seed=random_seed)
        if source_solver.check() != sat:
            raise RuntimeError("staged regular-class source did not solve")
        solver, data = build(
            3, timeout_ms, True, all_regular_classes=True,
            hole_reciprocity=True, hole_full_pack_overlap_cap=True,
        )
        freeze_outer(source_data, source_solver.model(), solver, data)
    else:
        solver, data = build(
            3, timeout_ms, True,
            diagonal_rows=diagonal_rows,
            all_regular_classes=all_regular_classes,
            hole_reciprocity=True,
            hole_full_pack_overlap_cap=True,
            regular_class_indices=regular_class_indices,
        )
        solver.set(random_seed=random_seed)
    if solver.check() != sat:
        raise RuntimeError("exact two-sixpack model did not solve")
    model = solver.model()

    def chosen(mapping):
        return sorted(
            key for key, value in mapping.items()
            if is_true(model.eval(value, model_completion=True))
        )

    blocks = []
    for class_map in data["classes"]:
        blocks.extend(chosen(class_map))
    blocks.extend(chosen(data["holes"]))
    marked = chosen(data["marked_pairs"])
    for missing_color in range(3):
        blocks.extend([
            edge for edge in marked
            if missing_color not in {color(edge[0]), color(edge[1])}
        ])
    outer_payload = {
        "branch": 3,
        "blocks": [list(block) for block in blocks],
        "k_edges": [list(edge) for edge in chosen(data["k"])],
    }
    system = fixed_system(outer_payload)
    covers = []
    for triples, pairs in zip(
            data["sixpack_triple_neighbors"],
            data["sixpack_pair_neighbors"]):
        covers.append(set().union(*(
            set(block) for block in chosen(triples) + chosen(pairs)
        )))
    overlap = sorted(covers[0] & covers[1])
    single_optima = {
        point: unit_nondiagonal_fiber_optimum(
            system, point, include_diagonal=True)
        for point in overlap
    } if genuine_only or details else {}
    genuine_pairs = [
        pair for pair in combinations(overlap, 2)
        if not single_optima[pair[0]]["strict"]
        and not single_optima[pair[1]]["strict"]
    ] if single_optima else []
    strict_single_points = [
        point for point in overlap if single_optima[point]["strict"]
    ] if single_optima else []
    for scale in range(1, max_scale + 1):
        for p, q in combinations(overlap, 2):
            if genuine_only and (
                    single_optima[p]["strict"] or single_optima[q]["strict"]):
                continue
            if (certificate := scaled_joint_cover(
                    system, p, q, scale, details=details)):
                answer = {
                    "overlap_card": len(overlap), "certificate": certificate
                }
                if genuine_only:
                    answer["genuine_pair_count"] = len(genuine_pairs)
                    answer["strict_single_points"] = strict_single_points
                if details:
                    answer["outer_payload"] = outer_payload
                    answer["joint_optimum"] = exact_joint_optimum(system, p, q)
                    answer["single_fiber_optima"] = [
                        single_optima[point] for point in (p, q)
                    ]
                    answer["overlap_single_fiber_optima"] = [
                        single_optima[point] for point in overlap
                    ]
                return answer
    answer = {"overlap_card": len(overlap), "certificate": None}
    if genuine_only:
        answer["genuine_pair_count"] = len(genuine_pairs)
        answer["strict_single_points"] = strict_single_points
    return answer


def fixed_payload_model(payload: dict, max_scale: int, details: bool,
                        genuine_only: bool) -> dict:
    """Scan a stored outer payload with an explicit exceptional-cover overlap."""
    system = fixed_system(payload)
    overlap = sorted(payload["overlap_points"])
    single_optima = {
        point: unit_nondiagonal_fiber_optimum(
            system, point, include_diagonal=True)
        for point in overlap
    }
    strict_single_points = [
        point for point in overlap if single_optima[point]["strict"]
    ]
    genuine_pairs = [
        pair for pair in combinations(overlap, 2)
        if not single_optima[pair[0]]["strict"]
        and not single_optima[pair[1]]["strict"]
    ]
    for scale in range(1, max_scale + 1):
        for p, q in combinations(overlap, 2):
            if genuine_only and (
                    single_optima[p]["strict"] or single_optima[q]["strict"]):
                continue
            if (certificate := scaled_joint_cover(
                    system, p, q, scale, details=details)):
                answer = {
                    "overlap_card": len(overlap),
                    "certificate": certificate,
                    "genuine_pair_count": len(genuine_pairs),
                    "strict_single_points": strict_single_points,
                }
                if details:
                    answer["joint_optimum"] = exact_joint_optimum(system, p, q)
                    answer["overlap_single_fiber_optima"] = [
                        single_optima[point] for point in overlap
                    ]
                return answer
    return {
        "overlap_card": len(overlap),
        "certificate": None,
        "genuine_pair_count": len(genuine_pairs),
        "strict_single_points": strict_single_points,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--payload", type=Path)
    parser.add_argument("--samples", type=int, default=1)
    parser.add_argument("--seed-start", type=int, default=0)
    parser.add_argument("--max-scale", type=int, default=6)
    parser.add_argument("--timeout-seconds", type=int, default=60)
    parser.add_argument("--details", action="store_true")
    parser.add_argument(
        "--genuine-only", action="store_true",
        help="only scan pairs whose two single-fiber optima are non-strict",
    )
    parser.add_argument("--diagonal-rows", action="store_true")
    parser.add_argument("--all-regular-classes", action="store_true")
    parser.add_argument(
        "--stage-all-regular-classes", action="store_true",
        help=("generate a cap-only two-class outer, freeze it, then restore "
              "hole reciprocity before scanning prices"),
    )
    parser.add_argument(
        "--regular-class", action="append", type=int, choices=(1, 2),
    )
    args = parser.parse_args()
    if args.samples <= 0 or args.max_scale <= 0:
        parser.error("--samples and --max-scale must be positive")
    if args.all_regular_classes and args.regular_class is not None:
        parser.error("use either --all-regular-classes or --regular-class")
    if args.stage_all_regular_classes and (
            args.diagonal_rows or args.all_regular_classes
            or args.regular_class is not None):
        parser.error("--stage-all-regular-classes is a standalone scope")
    if args.payload is not None:
        if args.samples != 1:
            parser.error("--payload requires --samples 1")
        results = [fixed_payload_model(
            json.loads(args.payload.read_text()), args.max_scale,
            args.details, args.genuine_only)]
    else:
        results = [
            one_model(
                args.timeout_seconds * 1000, seed, args.max_scale, args.details,
                args.genuine_only, args.diagonal_rows, args.all_regular_classes,
                (tuple(args.regular_class)
                 if args.regular_class is not None else None),
                args.stage_all_regular_classes)
            for seed in range(args.seed_start, args.seed_start + args.samples)
        ]
    print(json.dumps(results, separators=(",", ":"), default=str))
    passed = sum(result["certificate"] is not None for result in results)
    print(f"joint_overlap_price_selector={passed}/{len(results)}")
    return 0 if passed == len(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
