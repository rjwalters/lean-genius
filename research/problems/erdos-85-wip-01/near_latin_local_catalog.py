#!/usr/bin/env python3
"""Exact local catalog for a doubled fiber pair in a near-Latin lift.

After relabeling the two fibers, their 2-regular bipartite graph is the union
of the identity matching and a permutation with prescribed cycle lengths.
This script enumerates every perfect matching inside each ten-point fiber and
counts the ordered pairs whose induced 20-vertex graph is C4-free.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter


def perfect_matchings(points: tuple[int, ...]):
    if not points:
        yield ()
        return
    x = points[0]
    for position in range(1, len(points)):
        y = points[position]
        rest = points[1:position] + points[position + 1:]
        for matching in perfect_matchings(rest):
            yield ((x, y),) + matching


def successor_from_cycle_type(r: int, cycle_type: tuple[int, ...]) -> list[int]:
    if sum(cycle_type) != r or any(length < 3 for length in cycle_type):
        raise ValueError("cycle lengths must sum to the fiber size and be at least 3")
    successor = list(range(r))
    start = 0
    for length in cycle_type:
        for x in range(start, start + length):
            successor[x] = start + (x - start + 1) % length
        start += length
    return successor


def edge_code(x: int, y: int) -> int:
    if x > y:
        x, y = y, x
    return 1 << (y * (y - 1) // 2 + x)


def catalog(r: int, cycle_type: tuple[int, ...]) -> dict[str, object]:
    matchings = list(perfect_matchings(tuple(range(r))))
    successor = successor_from_cycle_type(r, cycle_type)
    cross_neighbors = [{x, successor[x]} for x in range(r)]
    matching_masks = [sum(edge_code(x, y) for x, y in matching)
                      for matching in matchings]
    compatible_counts = []
    total = 0
    examples = []
    for left in matchings:
        # A C4 involving internal edges must consist of one left matching
        # edge, one right matching edge, and two cross edges.  Record exactly
        # the right edges forbidden by this left matching.
        forbidden = 0
        for x, xp in left:
            for y in cross_neighbors[x]:
                for yp in cross_neighbors[xp]:
                    if y != yp:
                        forbidden |= edge_code(y, yp)
        valid_indices = [index for index, mask in enumerate(matching_masks)
                         if not (mask & forbidden)]
        compatible_counts.append(len(valid_indices))
        total += len(valid_indices)
        if valid_indices and len(examples) < 3:
            examples.append({"left": left, "right": matchings[valid_indices[0]]})
    return {
        "fiber_size": r,
        "doubled_pair_cycle_type": [2 * length for length in cycle_type],
        "perfect_matchings_per_fiber": len(matchings),
        "compatible_ordered_pairs": total,
        "compatible_right_count_min": min(compatible_counts),
        "compatible_right_count_max": max(compatible_counts),
        "compatible_right_count_histogram": dict(sorted(Counter(
            compatible_counts).items())),
        "examples": examples,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fiber-size", type=int, default=10)
    parser.add_argument(
        "--cycle-types", nargs="*", default=("10", "3+7", "4+6", "5+5"),
        help="cycle lengths of the relative permutation, not doubled graph cycles",
    )
    args = parser.parse_args()
    if args.fiber_size % 2:
        parser.error("fiber size must be even")
    results = []
    for raw in args.cycle_types:
        cycle_type = tuple(map(int, raw.split("+")))
        results.append(catalog(args.fiber_size, cycle_type))
    print(json.dumps(results, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
