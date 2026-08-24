#!/usr/bin/env python3
"""Minimal abstract counterexample to a generic two-color selector lemma.

The four parity triples in a 2x2x2 cube form a linear three-partite
hypergraph with matching number one.  Nevertheless, after omitting any one
color, the projection is a four-cycle and has vertex-cover number two.  Thus
a rank deficit at demand two does not by itself imply a strict two-color
point cover; the q=9 proof must use outer structure that excludes (or handles)
this Pasch configuration.
"""

from itertools import combinations
import json


BLOCKS = (
    frozenset((0, 8, 16)),
    frozenset((0, 9, 17)),
    frozenset((1, 8, 17)),
    frozenset((1, 9, 16)),
)


def maximum_disjoint_family() -> int:
    return max(
        len(chosen)
        for size in range(len(BLOCKS) + 1)
        for chosen in combinations(BLOCKS, size)
        if all(first.isdisjoint(second)
               for first, second in combinations(chosen, 2))
    )


def projected_cover_number(omitted: int) -> int:
    retained = {
        point for color in range(3) if color != omitted
        for point in range(8 * color, 8 * color + 2)
    }
    projected = [block & retained for block in BLOCKS]
    return min(
        len(cover)
        for size in range(len(retained) + 1)
        for cover_tuple in combinations(sorted(retained), size)
        if (cover := set(cover_tuple)) is not None
        and all(cover & block for block in projected)
    )


def main() -> None:
    linear = all(
        len(first & second) <= 1
        for first, second in combinations(BLOCKS, 2)
    )
    matching_number = maximum_disjoint_family()
    cover_numbers = [projected_cover_number(color) for color in range(3)]
    if not linear or matching_number != 1 or cover_numbers != [2, 2, 2]:
        raise RuntimeError("Pasch counterexample audit failed")
    print(json.dumps({
        "blocks": [sorted(block) for block in BLOCKS],
        "linear": linear,
        "matching_number": matching_number,
        "demand": 2,
        "two_color_cover_numbers": cover_numbers,
        "strict_two_color_cover_exists": any(card < 2 for card in cover_numbers),
    }, separators=(",", ":")))


if __name__ == "__main__":
    main()
