#!/usr/bin/env python3
"""Exact bounded-denominator test for q=9 unit full-fiber covers.

For a U1 point p, put unit row price on all five B0 rows containing p and
use the reduced price mask: outgoing point prices at those five rows, plus
incoming compensation prices at p.  After multiplying all prices by k, the
cover problem is an integer linear system.  This script finds the least
denominator k (up to a requested bound) admitting total scaled cost at most
``k * degree_sum - 1`` and checks the returned integer vector directly.

The result is corpus evidence, not a theorem that denominator six works for
every admissible outer design.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp

from q9_symmetric_point_mass_obstruction import N_TRIPLE, N_U1, fixed_system


DEFAULT_PAYLOADS = (
    "q9_13f_counterexample.json",
    "q9_13t_counterexample.json",
    "q9_gram_fractional_gap_witness.json",
    "q9_branch4_row40_interval_witness.json",
)


def scaled_cover(system: dict, point: int, denominator: int):
    fiber = {
        row for row, block in enumerate(system["blocks"])
        if point in block
    }
    if len(fiber) != 5:
        raise RuntimeError(f"point {point} has full fiber {sorted(fiber)}")
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
        constraint = np.zeros(len(allowed), dtype=int)
        for q in system["blocks"][v]:
            index = system["cap_index"][u, q]
            if index in position:
                constraint[position[index]] += 1
        for q in system["blocks"][u]:
            index = system["cap_index"][v, q]
            if index in position:
                constraint[position[index]] += 1
        matrix.append(constraint)
        lower.append(denominator * need)
    degree_sum = sum(system["degree"][row] for row in fiber)
    constraints = [
        LinearConstraint(
            np.array(matrix), np.array(lower),
            np.full(len(matrix), np.inf),
        ),
        LinearConstraint(
            np.ones((1, len(allowed))), -np.inf,
            denominator * degree_sum - 1,
        ),
    ]
    result = milp(
        np.ones(len(allowed)), integrality=np.ones(len(allowed)),
        bounds=Bounds(
            np.zeros(len(allowed)),
            np.full(len(allowed), 2 * denominator),
        ),
        constraints=constraints,
        options={"mip_rel_gap": 0, "time_limit": 60},
    )
    if result.status == 2:  # HiGHS proved the integer system infeasible.
        return None
    if not result.success:
        raise RuntimeError(
            f"MILP did not decide p={point}, k={denominator}: "
            f"{result.message}"
        )
    prices = np.rint(result.x).astype(int)
    # Everything below is an exact integer audit, independent of MILP
    # feasibility tolerances.
    if np.any(prices < 0) or np.any(prices > 2 * denominator):
        raise RuntimeError("integer reconstruction violates price bounds")
    slacks = np.array(matrix, dtype=int) @ prices - np.array(lower, dtype=int)
    scaled_cost = int(prices.sum())
    if int(slacks.min()) < 0:
        raise RuntimeError("integer reconstruction violates a cover inequality")
    if scaled_cost >= denominator * degree_sum:
        raise RuntimeError("integer reconstruction lost the strict margin")
    return {
        "point": point,
        "fiber": sorted(fiber),
        "denominator": denominator,
        "scaled_cost": scaled_cost,
        "scaled_target": denominator * degree_sum,
        "minimum_scaled_slack": int(slacks.min()),
        "nonzero_price_count": int(np.count_nonzero(prices)),
        "prices": [
            [list(system["caps"][allowed[index]]), int(value)]
            for index, value in enumerate(prices) if value
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("payloads", type=Path, nargs="*")
    parser.add_argument("--max-denominator", type=int, default=12)
    parser.add_argument("--show-prices", action="store_true")
    parser.add_argument(
        "--middle-hole-only", action="store_true",
        help="test only the middle-color point on each exceptional hole row",
    )
    args = parser.parse_args()
    if args.max_denominator < 1:
        parser.error("--max-denominator must be positive")
    base = Path(__file__).resolve().parent
    payloads = args.payloads or [base / name for name in DEFAULT_PAYLOADS]

    summaries = []
    for path in payloads:
        system = fixed_system(json.loads(path.read_text()))
        points = list(range(N_U1))
        if args.middle_hole_only:
            hole_count = 2 if system["branch"] == 3 else 4
            hole_rows = range(N_TRIPLE - hole_count, N_TRIPLE)
            points = sorted({
                point for row in hole_rows for point in system["blocks"][row]
                if 8 <= point < 16
            })
            if len(points) != hole_count:
                raise RuntimeError(
                    f"expected {hole_count} middle-hole points, got {points}"
                )
        least = None
        witnesses = []
        for denominator in range(1, args.max_denominator + 1):
            witnesses = [
                witness for point in points
                if (witness := scaled_cover(system, point, denominator))
                is not None
            ]
            if witnesses:
                least = denominator
                break
        if least is None:
            raise SystemExit(
                f"{path.name}: no strict cover through denominator "
                f"{args.max_denominator}"
            )
        for witness in witnesses:
            if not args.show_prices:
                del witness["prices"]
        summaries.append({
            "payload": path.name,
            "branch": system["branch"],
            "least_denominator": least,
            "candidate_points": points,
            "witnesses": witnesses,
        })
    print(json.dumps(summaries, indent=2, sort_keys=True))
    print("bounded_denominator_full_fiber=EXACT")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
