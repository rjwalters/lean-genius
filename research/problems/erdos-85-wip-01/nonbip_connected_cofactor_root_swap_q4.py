#!/usr/bin/env python3
"""Cut the simplest triangle-root swap on cleared cofactor terms."""

from __future__ import annotations

import itertools

from binary_q4_fixed_free_disconnected_control import A_EDGES, N


def sign(permutation: tuple[int, ...]) -> int:
    inversions = sum(
        permutation[i] > permutation[j]
        for i in range(N)
        for j in range(i + 1, N)
    )
    return -1 if inversions % 2 else 1


def main() -> None:
    adjacency = [[0] * N for _ in range(N)]
    for left, right in A_EDGES:
        adjacency[left][right] = adjacency[right][left] = 1
    triangles = [
        triple
        for triple in itertools.combinations(range(N), 3)
        if all(adjacency[u][v] for u, v in itertools.combinations(triple, 2))
    ]
    triangle_degree = [0] * N
    for triple in triangles:
        for vertex in triple:
            triangle_degree[vertex] += 1
    core = [row[:] for row in adjacency]
    for triple in triangles:
        for left, right in itertools.combinations(triple, 2):
            core[left][right] = core[right][left] = 0
    for vertex in range(N):
        core[vertex][vertex] = -triangle_degree[vertex]

    triangle = triangles[0]

    def entry(root: int, row: int, column: int) -> int:
        return 1 if column == root else core[row][column]

    def weight(root: int, permutation: tuple[int, ...]) -> int:
        answer = sign(permutation)
        for row, column in enumerate(permutation):
            answer *= entry(root, row, column)
        return answer

    def selected_swap(
        root: int, permutation: tuple[int, ...]
    ) -> tuple[int, tuple[int, ...]] | None:
        for target in triangle:
            if target == root:
                continue
            switched = tuple(
                target if column == root else root if column == target else column
                for column in permutation
            )
            old_weight = weight(root, permutation)
            new_weight = weight(target, switched)
            if new_weight == -old_weight:
                return target, switched
        return None

    checked = 0
    counterexample = None

    def enumerate_terms(
        root: int, row: int, used: set[int], prefix: list[int]
    ) -> bool:
        nonlocal checked, counterexample
        if row == N:
            permutation = tuple(prefix)
            checked += 1
            image = selected_swap(root, permutation)
            if image is None:
                counterexample = ("no_valid_swap", root, permutation, weight(root, permutation))
                return False
            target, switched = image
            reverse = selected_swap(target, switched)
            if reverse != (root, permutation):
                counterexample = (
                    "not_involutive",
                    root,
                    permutation,
                    target,
                    switched,
                    reverse,
                )
                return False
            return True
        for column in range(N):
            if column not in used and entry(root, row, column) != 0:
                if not enumerate_terms(root, row + 1, used | {column}, prefix + [column]):
                    return False
        return True

    for root in triangle:
        if not enumerate_terms(root, 0, set(), []):
            break
    assert counterexample is not None
    print(f"triangle={triangle}; checked_terms={checked}")
    print(f"counterexample={counterexample}")
    print("canonical lexicographic triangle-root column swap is cut")


if __name__ == "__main__":
    main()
