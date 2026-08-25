#!/usr/bin/env python3
"""Verify failure of reverse-interval submodular uncrossing for (13bo)."""

import json
from pathlib import Path

from q9_symmetric_point_mass_obstruction import (
    N,
    fixed_system,
    local_packing_family,
)


PAYLOAD = Path(__file__).with_name(
    "q9_branch4_exceptional_price_support_counterexample.json"
)


def main():
    with PAYLOAD.open(encoding="utf-8") as stream:
        system = fixed_system(json.load(stream))
    families = {row: local_packing_family(system, row) for row in range(N)}
    assert all(families.values())

    forced = {}
    possible = {}
    for row in range(N):
        forced[row] = set(families[row][0])
        possible[row] = set()
        for packing in families[row]:
            forced[row] &= set(packing)
            possible[row] |= set(packing)

    def interval(target):
        lower = {row for row in range(N) if target in forced[row]}
        upper = {row for row in range(N) if target not in possible[row]}
        return lower, upper

    def hit(family, rows):
        return min(len(packing & rows) for packing in family)

    def satisfaction(family, lower, upper):
        return max(
            len(packing & lower) + len(upper - packing)
            for packing in family
        )

    family = families[0]
    lower1, upper1 = interval(1)
    lower8, upper8 = interval(8)
    assert not lower1 and not lower8
    assert (len(upper1), len(upper8)) == (37, 37)
    assert (
        hit(family, upper1),
        hit(family, upper8),
        hit(family, upper1 & upper8),
        hit(family, upper1 | upper8),
    ) == (3, 3, 1, 4)

    # The upper-hit function is not supermodular on actual reverse intervals.
    assert (
        hit(family, upper1) + hit(family, upper8)
        > hit(family, upper1 & upper8) + hit(family, upper1 | upper8)
    )

    # Equivalently, maximum signed boundary satisfaction is not submodular.
    left = (
        satisfaction(family, lower1, upper1)
        + satisfaction(family, lower8, upper8)
    )
    right = (
        satisfaction(family, lower1 & lower8, upper1 & upper8)
        + satisfaction(family, lower1 | lower8, upper1 | upper8)
    )
    assert (left, right) == (68, 69)
    assert left < right
    print("verified: actual reverse intervals 1 and 8 violate uncrossing")
    print("upper-hit values: 3 + 3 > 1 + 4")
    print("signed satisfaction values: 68 < 69")


if __name__ == "__main__":
    main()
