#!/usr/bin/env python3
"""Small abstract counterexamples to a generic two-color selector lemma.

Already three parity triples form a loose triangle: a linear three-partite
hypergraph with matching number one whose every two-color projection has
vertex-cover number two.  The four-triple Pasch merely extends it.  Thus a
rank deficit at demand two does not by itself imply a strict two-color point
cover, even under Pasch-freeness.
"""

from itertools import combinations
import json


TRIANGLE = (
    frozenset((0, 8, 16)),
    frozenset((0, 9, 17)),
    frozenset((1, 8, 17)),
)
PASCH = TRIANGLE + (
    frozenset((1, 9, 16)),
)


def maximum_disjoint_family(blocks) -> int:
    return max(
        len(chosen)
        for size in range(len(blocks) + 1)
        for chosen in combinations(blocks, size)
        if all(first.isdisjoint(second)
               for first, second in combinations(chosen, 2))
    )


def projected_cover_number(blocks, omitted: int) -> int:
    retained = {
        point for color in range(3) if color != omitted
        for point in range(8 * color, 8 * color + 2)
    }
    projected = [block & retained for block in blocks]
    return min(
        len(cover)
        for size in range(len(retained) + 1)
        for cover_tuple in combinations(sorted(retained), size)
        if (cover := set(cover_tuple)) is not None
        and all(cover & block for block in projected)
    )


def audit(name: str, blocks) -> dict:
    linear = all(
        len(first & second) <= 1
        for first, second in combinations(blocks, 2)
    )
    matching_number = maximum_disjoint_family(blocks)
    cover_numbers = [projected_cover_number(blocks, color) for color in range(3)]
    if not linear or matching_number != 1 or cover_numbers != [2, 2, 2]:
        raise RuntimeError(f"{name} counterexample audit failed")
    return {
        "name": name,
        "blocks": [sorted(block) for block in blocks],
        "linear": linear,
        "matching_number": matching_number,
        "demand": 2,
        "two_color_cover_numbers": cover_numbers,
        "strict_two_color_cover_exists": any(card < 2 for card in cover_numbers),
    }


def main() -> None:
    print(json.dumps({
        "counterexamples": [
            audit("loose_triangle", TRIANGLE),
            audit("pasch", PASCH),
        ]
    }, separators=(",", ":")))


if __name__ == "__main__":
    main()
