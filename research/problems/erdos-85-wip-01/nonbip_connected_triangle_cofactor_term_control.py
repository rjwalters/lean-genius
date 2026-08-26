#!/usr/bin/env python3
"""Audit termwise cancellation in one triangle's adjugate row sums."""

from __future__ import annotations

import collections
import itertools

import sympy

from binary_q4_fixed_free_disconnected_control import A_EDGES, N


def cofactor_terms(matrix: list[list[int]], adjugate_row: int) -> list[int]:
    terms: list[int] = []
    for deleted_row in range(N):
        rows = [row for row in range(N) if row != deleted_row]
        columns = [column for column in range(N) if column != adjugate_row]
        column_position = {column: position for position, column in enumerate(columns)}

        def enumerate_terms(
            position: int, used: set[int], permutation: list[int], product: int
        ) -> None:
            if position == len(rows):
                inversions = sum(
                    permutation[left] > permutation[right]
                    for left in range(len(permutation))
                    for right in range(left + 1, len(permutation))
                )
                sign = -1 if (inversions + deleted_row + adjugate_row) % 2 else 1
                terms.append(sign * product)
                return
            row = rows[position]
            for column in columns:
                value = matrix[row][column]
                if column in used or value == 0:
                    continue
                enumerate_terms(
                    position + 1,
                    used | {column},
                    permutation + [column_position[column]],
                    product * value,
                )

        enumerate_terms(0, set(), [], 1)
    return terms


def main() -> None:
    adjacency = [[0] * N for _ in range(N)]
    for left, right in A_EDGES:
        adjacency[left][right] = adjacency[right][left] = 1
    triangles = [
        triple
        for triple in itertools.combinations(range(N), 3)
        if all(adjacency[left][right] for left, right in itertools.combinations(triple, 2))
    ]
    triangle_degrees = [sum(vertex in triple for triple in triangles) for vertex in range(N)]
    core = [row[:] for row in adjacency]
    for triple in triangles:
        for left, right in itertools.combinations(triple, 2):
            core[left][right] = core[right][left] = 0
    for vertex in range(N):
        core[vertex][vertex] = -triangle_degrees[vertex]

    triangle = triangles[0]
    all_terms: list[int] = []
    row_sums = []
    for vertex in triangle:
        terms = cofactor_terms(core, vertex)
        all_terms.extend(terms)
        row_sums.append(sum(terms))

    exact = sympy.Matrix(core)
    adjugate_times_one = exact.adjugate() * sympy.ones(N, 1)
    assert row_sums == [int(adjugate_times_one[vertex]) for vertex in triangle]
    assert row_sums == [384, 384, -768]
    assert sum(all_terms) == 0

    by_magnitude = {
        magnitude: (
            sum(term == magnitude for term in all_terms),
            sum(term == -magnitude for term in all_terms),
        )
        for magnitude in sorted(set(map(abs, all_terms)))
    }
    assert by_magnitude == {128: (52, 46), 256: (42, 45)}

    print(f"triangle={triangle}")
    print(f"adjugate_row_sums={row_sums}")
    print(f"term_sign_counts_by_magnitude={by_magnitude}")
    print("total_triangle_cofactor_sum=0")
    print("pairwise_weight_preserving_involution=false")


if __name__ == "__main__":
    main()
