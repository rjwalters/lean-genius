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
uniform theorem.
"""

from __future__ import annotations

import argparse
import json
from itertools import combinations

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from z3 import is_true, sat

from q9_b0_residual_defect_sat import color
from q9_exceptional_hole_sixpack_sat import build
from q9_symmetric_point_mass_obstruction import fixed_system


def scaled_joint_cover(system: dict, p: int, q: int, scale: int):
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
    return {
        "points": [p, q],
        "scale": scale,
        "scaled_cost": scaled_cost,
        "scaled_target": scale * target,
        "minimum_scaled_slack": int(slacks.min()),
    }


def one_model(timeout_ms: int, random_seed: int, max_scale: int):
    solver, data = build(
        3, timeout_ms, True,
        hole_reciprocity=True,
        hole_full_pack_overlap_cap=True,
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
    system = fixed_system({
        "branch": 3,
        "blocks": blocks,
        "k_edges": chosen(data["k"]),
    })
    covers = []
    for triples, pairs in zip(
            data["sixpack_triple_neighbors"],
            data["sixpack_pair_neighbors"]):
        covers.append(set().union(*(
            set(block) for block in chosen(triples) + chosen(pairs)
        )))
    overlap = sorted(covers[0] & covers[1])
    for scale in range(1, max_scale + 1):
        for p, q in combinations(overlap, 2):
            if (certificate := scaled_joint_cover(system, p, q, scale)):
                return {"overlap_card": len(overlap), "certificate": certificate}
    return {"overlap_card": len(overlap), "certificate": None}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=1)
    parser.add_argument("--max-scale", type=int, default=6)
    parser.add_argument("--timeout-seconds", type=int, default=60)
    args = parser.parse_args()
    if args.samples <= 0 or args.max_scale <= 0:
        parser.error("--samples and --max-scale must be positive")
    results = [
        one_model(args.timeout_seconds * 1000, seed, args.max_scale)
        for seed in range(args.samples)
    ]
    print(json.dumps(results, separators=(",", ":")))
    passed = sum(result["certificate"] is not None for result in results)
    print(f"joint_overlap_price_selector={passed}/{len(results)}")
    return 0 if passed == len(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
