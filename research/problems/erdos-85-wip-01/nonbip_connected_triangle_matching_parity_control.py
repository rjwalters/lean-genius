#!/usr/bin/env python3
"""Test whether triangle/K edge parity controls matching-switch sign."""

from __future__ import annotations

import itertools
from collections import Counter

from binary_q4_fixed_free_disconnected_control import A_EDGES, N, adjacency


def main() -> None:
    graph_edges = {tuple(sorted(edge)) for edge in A_EDGES}
    neighbors = adjacency(A_EDGES)
    triangles = [
        triple
        for triple in itertools.combinations(range(N), 3)
        if all(
            tuple(sorted(edge)) in graph_edges
            for edge in itertools.combinations(triple, 2)
        )
    ]
    triangle_edges = {
        tuple(sorted(edge))
        for triple in triangles
        for edge in itertools.combinations(triple, 2)
    }
    remainder_edges = graph_edges - triangle_edges
    assert len(triangles) == len(remainder_edges) == 8

    matchings: list[tuple[int, ...]] = []

    def enumerate_matchings(row: int, used: set[int], prefix: list[int]) -> None:
        if len(matchings) >= 12:
            return
        if row == N:
            matchings.append(tuple(prefix))
            return
        for column in sorted(neighbors[row] - used):
            enumerate_matchings(row + 1, used | {column}, prefix + [column])

    enumerate_matchings(0, set(), [])
    assert len(matchings) == 12

    profiles: Counter[tuple[int, int]] = Counter()
    examples: dict[tuple[int, int], tuple[int, int]] = {}
    for matching in matchings:
        outgoing = [
            [
                target
                for target in range(N)
                if target != row and matching[target] in neighbors[row]
            ]
            for row in range(N)
        ]

        def search(root: int, vertex: int, path: list[int]) -> None:
            for target in outgoing[vertex]:
                if target == root and len(path) >= 3:
                    remainder_count = 0
                    for left, right in zip(path, path[1:] + path[:1]):
                        remainder_count += (
                            tuple(sorted((left, matching[left]))) in remainder_edges
                        )
                        remainder_count += (
                            tuple(sorted((left, matching[right]))) in remainder_edges
                        )
                    profile = (len(path) % 2, remainder_count % 2)
                    profiles[profile] += 1
                    examples.setdefault(profile, (len(path), remainder_count))
                elif target > root and target not in path:
                    search(root, target, path + [target])

        for root in range(N):
            search(root, root, [root])

    expected = Counter(
        {
            (1, 1): 20377,
            (1, 0): 19864,
            (0, 0): 19735,
            (0, 1): 18755,
        }
    )
    assert profiles == expected
    assert examples == {
        (1, 0): (5, 6),
        (0, 0): (8, 8),
        (1, 1): (13, 9),
        (0, 1): (12, 9),
    }
    print("verified triangle/K parity does not control matching-switch sign")
    print(f"profiles={dict(sorted(profiles.items()))}")
    print(f"first_examples={dict(sorted(examples.items()))}")


if __name__ == "__main__":
    main()
