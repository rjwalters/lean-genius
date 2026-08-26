#!/usr/bin/env python3
"""Test grouped/colored cofactor terms under single-cycle exchange at q=4."""

from __future__ import annotations

import itertools
import math

import networkx as nx

from binary_q4_fixed_free_disconnected_control import A_EDGES, N


def cofactor_terms(
    matrix: list[list[int]], root: int
) -> list[tuple[int, tuple[int, ...]]]:
    terms: list[tuple[int, tuple[int, ...]]] = []
    for deleted_row in range(N):
        rows = [row for row in range(N) if row != deleted_row]
        columns = [column for column in range(N) if column != root]

        def visit(position: int, used: set[int], mapping: list[int], product: int) -> None:
            if position == len(rows):
                permutation = [-1] * N
                permutation[deleted_row] = root
                for row, column in zip(rows, mapping):
                    permutation[row] = column
                inversions = sum(
                    permutation[i] > permutation[j]
                    for i in range(N)
                    for j in range(i + 1, N)
                )
                terms.append(((-1 if inversions % 2 else 1) * product, tuple(permutation)))
                return
            row = rows[position]
            for column in columns:
                value = matrix[row][column]
                if column not in used and value:
                    visit(position + 1, used | {column}, mapping + [column], product * value)

        visit(0, set(), [], 1)
    return terms


def cycle_lengths(left: tuple[int, ...], right: tuple[int, ...]) -> list[int]:
    inverse_left = [0] * N
    for row, column in enumerate(left):
        inverse_left[column] = row
    quotient = [inverse_left[right[row]] for row in range(N)]
    unseen = set(range(N))
    nontrivial = []
    while unseen:
        vertex = min(unseen)
        length = 0
        while vertex in unseen:
            unseen.remove(vertex)
            length += 1
            vertex = quotient[vertex]
        if length > 1:
            nontrivial.append(length)
    return nontrivial


def main() -> None:
    adjacency = [[0] * N for _ in range(N)]
    for left, right in A_EDGES:
        adjacency[left][right] = adjacency[right][left] = 1
    triangles = [
        triple
        for triple in itertools.combinations(range(N), 3)
        if all(adjacency[u][v] for u, v in itertools.combinations(triple, 2))
    ]
    triangle_degree = [sum(v in triple for triple in triangles) for v in range(N)]
    core = [row[:] for row in adjacency]
    for triple in triangles:
        for u, v in itertools.combinations(triple, 2):
            core[u][v] = core[v][u] = 0
    for vertex in range(N):
        core[vertex][vertex] = -triangle_degree[vertex]

    triangle = triangles[0]
    raw = [term for root in triangle for term in cofactor_terms(core, root)]
    unit = math.gcd(*(abs(value) for value, _ in raw))
    assert unit == 128
    expanded = [
        (1 if value > 0 else -1, permutation, copy)
        for value, permutation in raw
        for copy in range(abs(value) // unit)
    ]
    positive = [i for i, term in enumerate(expanded) if term[0] > 0]
    negative = [i for i, term in enumerate(expanded) if term[0] < 0]
    assert len(positive) == len(negative) == 136

    exchange = nx.Graph()
    exchange.add_nodes_from(positive, bipartite=0)
    exchange.add_nodes_from(negative, bipartite=1)
    for left in positive:
        for right in negative:
            lengths = cycle_lengths(expanded[left][1], expanded[right][1])
            if len(lengths) == 1 and lengths[0] % 2 == 0:
                exchange.add_edge(left, right)
    pairing = nx.algorithms.bipartite.maximum_matching(exchange, top_nodes=set(positive))

    two_cycle_exchange = exchange.copy()
    for left in positive:
        for right in negative:
            lengths = cycle_lengths(expanded[left][1], expanded[right][1])
            if len(lengths) <= 2 and sum(length - 1 for length in lengths) % 2 == 1:
                two_cycle_exchange.add_edge(left, right)
    two_cycle_pairing = nx.algorithms.bipartite.maximum_matching(
        two_cycle_exchange, top_nodes=set(positive)
    )

    print(f"triangle={triangle}; raw_terms={len(raw)}; unit={unit}")
    print(f"expanded_signs={len(positive)}/{len(negative)}")
    print(f"single_cycle_edges={exchange.number_of_edges()}")
    print(f"paired={len(pairing) // 2}/{len(positive)}")
    print(f"isolated={sum(exchange.degree(v) == 0 for v in exchange)}")
    print(f"at_most_two_cycle_edges={two_cycle_exchange.number_of_edges()}")
    print(f"at_most_two_cycle_paired={len(two_cycle_pairing) // 2}/{len(positive)}")
    assert len(pairing) == 2 * 132
    assert len(two_cycle_pairing) == 2 * 132


if __name__ == "__main__":
    main()
