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


def exact_joint_optimum_summary(system: dict, pair,
                                single_optima: dict) -> dict:
    """Summarize exact joint cost and its saving over two single covers."""
    optimum = exact_joint_optimum(system, *pair)
    joint_cost = Fraction(optimum["cost"])
    single_sum = sum(
        (Fraction(single_optima[point]["cost"]) for point in pair),
        Fraction(),
    )
    return {
        "points": list(pair),
        **{
            key: value for key, value in optimum.items()
            if key not in ("point_prices", "dual_edges")
        },
        "single_sum": str(single_sum),
        "uncrossing_gain": str(single_sum - joint_cost),
        "target_gap": str(Fraction(54) - joint_cost),
    }


def integer_single_optimum_cost(system: dict, optimum: dict) -> int:
    """Exactly audit the minimum integral cost for one unit fiber."""
    point = optimum["point"]
    fiber = set(optimum["support"])
    allowed = [
        index for index, (row, q) in enumerate(system["caps"])
        if row in fiber or q == point
    ]
    position = {old: new for new, old in enumerate(allowed)}
    matrix = []
    lower = []
    for u, v in system["edges"]:
        need = int(u in fiber) + int(v in fiber)
        if not need:
            continue
        row = np.zeros(len(allowed), dtype=int)
        for q in system["blocks"][v]:
            index = system["cap_index"][u, q]
            if index in position:
                row[position[index]] += 1
        for q in system["blocks"][u]:
            index = system["cap_index"][v, q]
            if index in position:
                row[position[index]] += 1
        matrix.append(row)
        lower.append(need)
    result = milp(
        np.ones(len(allowed)), integrality=np.ones(len(allowed)),
        bounds=Bounds(0, 2),
        constraints=LinearConstraint(
            np.array(matrix), np.array(lower), np.inf),
        options={"mip_rel_gap": 0, "time_limit": 60},
    )
    if not result.success:
        raise RuntimeError("integer single-cover MILP failed: " + result.message)
    prices = np.rint(result.x).astype(int)
    if (np.any(prices < 0) or np.any(prices > 2)
            or np.any(np.array(matrix, dtype=int) @ prices
                      < np.array(lower, dtype=int))):
        raise RuntimeError("integer single-cover reconstruction failed")
    return int(prices.sum())


def integer_single_dual_packing(system: dict, optimum: dict) -> dict:
    """Maximize the integral unit-capacity edge packing dual."""
    point = optimum["point"]
    fiber = set(optimum["support"])
    allowed = [
        index for index, (row, q) in enumerate(system["caps"])
        if row in fiber or q == point
    ]
    position = {old: new for new, old in enumerate(allowed)}
    edges = []
    matrix = []
    needs = []
    for u, v in system["edges"]:
        need = int(u in fiber) + int(v in fiber)
        if not need:
            continue
        row = np.zeros(len(allowed), dtype=int)
        for q in system["blocks"][v]:
            index = system["cap_index"][u, q]
            if index in position:
                row[position[index]] += 1
        for q in system["blocks"][u]:
            index = system["cap_index"][v, q]
            if index in position:
                row[position[index]] += 1
        edges.append((u, v))
        matrix.append(row)
        needs.append(need)
    result = milp(
        -np.array(needs, dtype=float), integrality=np.ones(len(edges)),
        bounds=Bounds(0, 1),
        constraints=LinearConstraint(
            np.array(matrix, dtype=int).T, -np.inf, 1),
        options={"mip_rel_gap": 0, "time_limit": 60},
    )
    if not result.success:
        raise RuntimeError("integer single-dual MILP failed: " + result.message)
    chosen = np.rint(result.x).astype(int)
    if (np.any(chosen < 0) or np.any(chosen > 1)
            or np.any(np.array(matrix, dtype=int).T @ chosen > 1)):
        raise RuntimeError("integer single-dual reconstruction failed")
    return {
        "value": int(np.array(needs, dtype=int) @ chosen),
        "edge_card": int(chosen.sum()),
        "internal_edge_card": sum(
            bool(chosen[i]) and u in fiber and v in fiber
            for i, (u, v) in enumerate(edges)
        ),
    }


def single_optimum_summary(system: dict, single_optima: dict) -> dict:
    """Expose the strict/tight/excess trichotomy without bulky LP witnesses."""
    costs = {
        str(point): optimum["cost"]
        for point, optimum in single_optima.items()
    }
    tight = [
        point for point, optimum in single_optima.items()
        if Fraction(optimum["cost"]) == optimum["target"]
    ]
    excesses = {
        str(point): str(
            Fraction(optimum["cost"]) - optimum["target"])
        for point, optimum in single_optima.items()
        if not optimum["strict"]
    }
    tight_packings = []
    for point in tight:
        optimum = single_optima[point]
        fiber = set(optimum["support"])
        primal_weights = [
            Fraction(weight) for _, weight in optimum["point_prices"]
        ]
        dual_edges = [
            (edge, Fraction(weight))
            for edge, weight in optimum["_dual_edges"] if weight
        ]
        integer_dual = integer_single_dual_packing(system, optimum)
        tight_packings.append({
            "point": point,
            "unit_primal": all(weight == 1 for weight in primal_weights),
            "primal_support_card": len(primal_weights),
            "unit_dual": all(weight == 1 for _, weight in dual_edges),
            "dual_edge_card": len(dual_edges),
            "internal_dual_edge_card": sum(
                u in fiber and v in fiber for (u, v), _ in dual_edges
            ),
            "integer_optimum_cost": integer_single_optimum_cost(
                system, optimum),
            "integer_dual_value": integer_dual["value"],
            "integer_dual_edge_card": integer_dual["edge_card"],
            "integer_dual_internal_edge_card": integer_dual[
                "internal_edge_card"],
        })
    return {
        "single_fiber_costs": costs,
        "tight_single_points": tight,
        "nonstrict_single_excesses": excesses,
        "tight_single_packings": tight_packings,
    }


def anchor_pair_summary(system: dict, hole_overlap: list[list[int]],
                        single_optima: dict) -> dict | None:
    """Audit the distinguished pair when both anchor cuts are singletons."""
    if len(hole_overlap) != 2 or any(len(points) != 1
                                     for points in hole_overlap):
        return None
    pair = (hole_overlap[0][0], hole_overlap[1][0])
    if pair[0] == pair[1]:
        return {"points": list(pair), "distinct": False}
    optimum = exact_joint_optimum(system, *pair)
    cost = Fraction(optimum["cost"])
    return {
        "points": list(pair),
        "distinct": True,
        "single_strict": [single_optima[p]["strict"] for p in pair],
        "single_costs": [single_optima[p]["cost"] for p in pair],
        "joint_cost": str(cost),
        "joint_strict": cost < 54,
        "target_gap": str(Fraction(54) - cost),
    }


def add_exact_joint_scan(answer: dict, system: dict, genuine_pairs,
                         single_optima: dict) -> None:
    """Attach all joint optima and the surviving tight-partner invariant."""
    joint_optima = [
        exact_joint_optimum_summary(system, pair, single_optima)
        for pair in genuine_pairs
    ]
    tight = {
        point for point, optimum in single_optima.items()
        if Fraction(optimum["cost"]) == optimum["target"]
    }
    partners = {point: [] for point in sorted(tight)}
    for optimum in joint_optima:
        if Fraction(optimum["target_gap"]) <= 0:
            continue
        p, q = optimum["points"]
        if p in tight:
            partners[p].append(q)
        if q in tight:
            partners[q].append(p)
    answer["genuine_joint_optima"] = joint_optima
    answer["tight_strict_partners"] = {
        str(point): values for point, values in partners.items()
    }
    answer["exists_tight_strict_partner"] = any(partners.values())


def one_model(
        timeout_ms: int, random_seed: int, max_scale: int,
        details: bool = False, genuine_only: bool = False,
        diagonal_rows: bool = False, all_regular_classes: bool = False,
        regular_class_indices: tuple[int, ...] | None = None,
        stage_all_regular_classes: bool = False,
        scan_exact_joint_optima: bool = False,
        anchor_pair_only: bool = False):
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
    hole_blocks = chosen(data["holes"])
    anchor_blocks = [chosen(anchor)[0] for anchor in data["sixpack_anchors"]]
    blocks.extend(hole_blocks)
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
        # Ordered with the two exceptional covers below, not lexicographically.
        "exceptional_hole_blocks": [list(block) for block in anchor_blocks],
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
    outer_payload["overlap_points"] = overlap
    exceptional_hole_overlap = [
        sorted(set(block) & set(overlap)) for block in anchor_blocks
    ]
    single_optima = {
        point: unit_nondiagonal_fiber_optimum(
            system, point, include_diagonal=True)
        for point in overlap
    } if (genuine_only or details or scan_exact_joint_optima
          or anchor_pair_only) else {}
    genuine_pairs = [
        pair for pair in combinations(overlap, 2)
        if not single_optima[pair[0]]["strict"]
        and not single_optima[pair[1]]["strict"]
    ] if single_optima else []
    strict_single_points = [
        point for point in overlap if single_optima[point]["strict"]
    ] if single_optima else []
    if anchor_pair_only:
        answer = {
            "overlap_card": len(overlap),
            "strict_single_points": strict_single_points,
            "exceptional_hole_overlap": exceptional_hole_overlap,
            "anchor_pair": anchor_pair_summary(
                system, exceptional_hole_overlap, single_optima),
        }
        if details:
            answer["outer_payload"] = outer_payload
        return answer
    for scale in range(1, max_scale + 1):
        for p, q in combinations(overlap, 2):
            if genuine_only and (
                    single_optima[p]["strict"] or single_optima[q]["strict"]):
                continue
            if (certificate := scaled_joint_cover(
                    system, p, q, scale, details=details)):
                answer = {
                    "overlap_card": len(overlap),
                    "exceptional_hole_overlap": exceptional_hole_overlap,
                    "certificate": certificate,
                }
                if genuine_only:
                    answer["genuine_pair_count"] = len(genuine_pairs)
                    answer["strict_single_points"] = strict_single_points
                    answer.update(single_optimum_summary(system, single_optima))
                    answer["anchor_pair"] = anchor_pair_summary(
                        system, exceptional_hole_overlap, single_optima)
                if details:
                    answer["outer_payload"] = outer_payload
                    answer["joint_optimum"] = exact_joint_optimum(system, p, q)
                    answer["single_fiber_optima"] = [
                        single_optima[point] for point in (p, q)
                    ]
                    answer["overlap_single_fiber_optima"] = [
                        single_optima[point] for point in overlap
                    ]
                if scan_exact_joint_optima:
                    add_exact_joint_scan(
                        answer, system, genuine_pairs, single_optima)
                return answer
    answer = {
        "overlap_card": len(overlap),
        "exceptional_hole_overlap": exceptional_hole_overlap,
        "certificate": None,
    }
    if genuine_only:
        answer["genuine_pair_count"] = len(genuine_pairs)
        answer["strict_single_points"] = strict_single_points
        answer.update(single_optimum_summary(system, single_optima))
        answer["anchor_pair"] = anchor_pair_summary(
            system, exceptional_hole_overlap, single_optima)
    if scan_exact_joint_optima:
        add_exact_joint_scan(answer, system, genuine_pairs, single_optima)
    if details:
        answer["outer_payload"] = outer_payload
        answer["overlap_single_fiber_optima"] = [
            single_optima[point] for point in overlap
        ]
    return answer


def fixed_payload_model(payload: dict, max_scale: int, details: bool,
                        genuine_only: bool,
                        scan_exact_joint_optima: bool = False,
                        anchor_pair_only: bool = False) -> dict:
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
    hole_blocks = payload.get(
        "exceptional_hole_blocks",
        payload["blocks"][24:26] if payload.get("branch") == 3 else [],
    )
    distinguished_hole_overlap = [
        sorted(set(block) & set(overlap))
        for block in hole_blocks
    ]
    if anchor_pair_only:
        return {
            "overlap_card": len(overlap),
            "strict_single_points": strict_single_points,
            "exceptional_hole_overlap": distinguished_hole_overlap,
            "anchor_pair": anchor_pair_summary(
                system, distinguished_hole_overlap, single_optima),
        }
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
                    "exceptional_hole_overlap": distinguished_hole_overlap,
                }
                answer.update(single_optimum_summary(system, single_optima))
                answer["anchor_pair"] = anchor_pair_summary(
                    system, distinguished_hole_overlap, single_optima)
                if details:
                    answer["joint_optimum"] = exact_joint_optimum(system, p, q)
                    answer["overlap_single_fiber_optima"] = [
                        single_optima[point] for point in overlap
                    ]
                if scan_exact_joint_optima:
                    add_exact_joint_scan(
                        answer, system, genuine_pairs, single_optima)
                return answer
    answer = {
        "overlap_card": len(overlap),
        "certificate": None,
        "genuine_pair_count": len(genuine_pairs),
        "strict_single_points": strict_single_points,
        "exceptional_hole_overlap": distinguished_hole_overlap,
    }
    answer.update(single_optimum_summary(system, single_optima))
    answer["anchor_pair"] = anchor_pair_summary(
        system, distinguished_hole_overlap, single_optima)
    if scan_exact_joint_optima:
        add_exact_joint_scan(answer, system, genuine_pairs, single_optima)
    return answer


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--payload", type=Path)
    parser.add_argument(
        "--save-payload", type=Path,
        help="write the first generated outer payload as durable JSON",
    )
    parser.add_argument("--samples", type=int, default=1)
    parser.add_argument("--seed-start", type=int, default=0)
    parser.add_argument("--max-scale", type=int, default=6)
    parser.add_argument("--timeout-seconds", type=int, default=60)
    parser.add_argument("--details", action="store_true")
    parser.add_argument("--scan-exact-joint-optima", action="store_true")
    parser.add_argument(
        "--anchor-pair-only", action="store_true",
        help="only audit the two exceptional anchor-overlap fibers and pair",
    )
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
            args.details, args.genuine_only, args.scan_exact_joint_optima,
            args.anchor_pair_only)]
    else:
        results = [
            one_model(
                args.timeout_seconds * 1000, seed, args.max_scale, args.details,
                args.genuine_only, args.diagonal_rows, args.all_regular_classes,
                (tuple(args.regular_class)
                 if args.regular_class is not None else None),
                args.stage_all_regular_classes, args.scan_exact_joint_optima,
                args.anchor_pair_only)
            for seed in range(args.seed_start, args.seed_start + args.samples)
        ]
    if args.save_payload is not None:
        if args.payload is not None or not args.details:
            parser.error(
                "--save-payload requires generated samples with --details")
        args.save_payload.write_text(
            json.dumps(results[-1]["outer_payload"], indent=2) + "\n")
    print(json.dumps(results, separators=(",", ":"), default=str))
    if args.anchor_pair_only:
        tested = sum(result["anchor_pair"] is not None for result in results)
        print(f"anchor_pair_audited={tested}/{len(results)}")
        return 0 if tested == len(results) else 1
    passed = sum(result["certificate"] is not None for result in results)
    print(f"joint_overlap_price_selector={passed}/{len(results)}")
    return 0 if passed == len(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
