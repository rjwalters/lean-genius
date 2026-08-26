#!/usr/bin/env python3
"""Exact q=4 calibration for signed Levi perfect-matching exchange.

Enumerate every perfect matching of the bipartite Levi graph of the banked
fixed-point-free q=4 control.  A move replaces one alternating cycle; it
changes determinant sign exactly when the cycle has even half-length.
The verifier checks local availability and constructs a full sign-reversing
pairing inside a deterministic sparse sample of the exchange graph.
"""

from __future__ import annotations

import random

import networkx as nx

from binary_q4_fixed_free_disconnected_control import A_EDGES, N, adjacency


def permutation_sign(permutation: tuple[int, ...]) -> int:
    inversions = sum(
        permutation[i] > permutation[j]
        for i in range(N)
        for j in range(i + 1, N)
    )
    return -1 if inversions % 2 else 1


def difference_cycle_lengths(
    left: tuple[int, ...], right: tuple[int, ...]
) -> list[int]:
    inverse_left = [0] * N
    for row, column in enumerate(left):
        inverse_left[column] = row
    quotient = [inverse_left[right[row]] for row in range(N)]
    unseen = set(range(N))
    lengths = []
    while unseen:
        root = min(unseen)
        vertex = root
        length = 0
        while vertex in unseen:
            unseen.remove(vertex)
            length += 1
            vertex = quotient[vertex]
        if length > 1:
            lengths.append(length)
    return sorted(lengths)


def is_sign_changing_single_cycle(
    left: tuple[int, ...], right: tuple[int, ...]
) -> bool:
    lengths = difference_cycle_lengths(left, right)
    return len(lengths) == 1 and lengths[0] % 2 == 0


def has_even_alternating_cycle(
    matching: tuple[int, ...], neighbors: list[set[int]]
) -> bool:
    # Contract the matching edges.  There is an arc i -> j when row i can
    # take the column currently assigned to row j.  A simple directed cycle
    # of even length is exactly a sign-changing alternating-cycle switch.
    outgoing = [
        [j for j in range(N) if j != i and matching[j] in neighbors[i]]
        for i in range(N)
    ]

    def search(root: int, vertex: int, seen: set[int], length: int) -> bool:
        for target in outgoing[vertex]:
            if target == root and length + 1 >= 4 and (length + 1) % 2 == 0:
                return True
            # Requiring root to be the least cycle vertex avoids duplicates.
            if target > root and target not in seen:
                if search(root, target, seen | {target}, length + 1):
                    return True
        return False

    return any(search(root, root, {root}, 0) for root in range(N))


def main() -> None:
    neighbors = adjacency(A_EDGES)
    matchings: list[tuple[int, ...]] = []

    def enumerate_matchings(row: int, used: set[int], prefix: list[int]) -> None:
        if row == N:
            matchings.append(tuple(prefix))
            return
        for column in sorted(neighbors[row] - used):
            enumerate_matchings(row + 1, used | {column}, prefix + [column])

    enumerate_matchings(0, set(), [])
    assert len(matchings) == 19_972
    positive = [i for i, matching in enumerate(matchings) if permutation_sign(matching) > 0]
    negative = [i for i, matching in enumerate(matchings) if permutation_sign(matching) < 0]
    assert len(positive) == len(negative) == 9_986
    assert all(has_even_alternating_cycle(matching, neighbors) for matching in matchings)

    # A deterministic sparse witness suffices to prove that the full
    # sign-changing exchange graph has a perfect matching.  Sample only 32
    # opposite-sign candidates for each positive matching, retaining a pair
    # exactly when their symmetric difference is one even alternating cycle.
    rng = random.Random(850073)
    exchange = nx.Graph()
    exchange.add_nodes_from(positive, bipartite=0)
    exchange.add_nodes_from(negative, bipartite=1)
    for left_index in positive:
        for right_index in rng.sample(negative, 32):
            if is_sign_changing_single_cycle(
                matchings[left_index], matchings[right_index]
            ):
                exchange.add_edge(left_index, right_index)
    assert exchange.number_of_edges() == 104_237

    pairing = nx.algorithms.bipartite.maximum_matching(
        exchange, top_nodes=set(positive)
    )
    assert len(pairing) == 2 * len(positive)
    for left_index in positive:
        right_index = pairing[left_index]
        assert right_index in negative
        assert pairing[right_index] == left_index
        assert is_sign_changing_single_cycle(
            matchings[left_index], matchings[right_index]
        )

    print("verified q=4 signed Levi matching-exchange calibration")
    print("perfect matchings = 19972; signs = 9986/9986")
    print("every matching has an even alternating-cycle switch")
    print("sparse exchange edges = 104237; paired = 9986")


if __name__ == "__main__":
    main()
