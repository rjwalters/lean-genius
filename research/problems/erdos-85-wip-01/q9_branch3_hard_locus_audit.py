#!/usr/bin/env python3
"""Separate easy one-row branch-3 obstructions from the reciprocity locus."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from q9_symmetric_point_mass_obstruction import (
    N,
    N_TRIPLE,
    dual,
    exact_certificate,
    fixed_system,
    random_outer,
    unit_row_cover_optimum,
)


def audit(system: dict) -> dict:
    if system["branch"] != 3:
        raise ValueError("hard-locus audit requires branch 3")
    one_row = []
    for row in range(N):
        certificate = unit_row_cover_optimum(system, row)
        if certificate is not None and certificate["strict"]:
            one_row.append({
                "row": row,
                "cost": certificate["cost"],
                "target": certificate["degree"],
            })

    holes_begin = N_TRIPLE - 2
    distinct_class = []
    for hole in range(holes_begin, N_TRIPLE):
        for first_class, second_class in ((0, 1), (0, 2), (1, 2)):
            for first in range(8 * first_class, 8 * first_class + 8):
                for second in range(8 * second_class, 8 * second_class + 8):
                    result = dual(system, {hole, first, second})
                    if not result.success:
                        continue
                    certificate = exact_certificate(system, result)
                    if certificate is None:
                        continue
                    distinct_class.append({
                        "hole": hole,
                        "regular_rows": [first, second],
                        "regular_classes": [first_class, second_class],
                        "margin": certificate["margin"],
                        "row_prices": certificate["row_prices"],
                        "point_price_count":
                            len(certificate["point_prices"]),
                    })
    return {
        "strict_one_row_count": len(one_row),
        "strict_one_row_certificates": one_row,
        "all_rows_fractionally_feasible": not one_row,
        "distinct_class_three_row_count": len(distinct_class),
        "has_distinct_class_three_row_certificate": bool(distinct_class),
        "distinct_class_three_row_certificates": distinct_class,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("payload", type=Path, nargs="?")
    parser.add_argument("--random-seed", type=int)
    parser.add_argument("--timeout-seconds", type=int, default=30)
    args = parser.parse_args()
    if args.payload is None:
        if args.random_seed is None:
            parser.error("provide a payload or --random-seed")
        payload = random_outer(3, args.random_seed, args.timeout_seconds)
    else:
        payload = json.loads(args.payload.read_text())
    print(json.dumps(
        audit(fixed_system(payload)), separators=(",", ":")
    ))


if __name__ == "__main__":
    main()
