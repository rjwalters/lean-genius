#!/usr/bin/env python3
"""Bounded q=4 test of quotienting Levi matchings by triangle flips."""

from __future__ import annotations

from collections import Counter

import networkx as nx

from binary_q4_fixed_free_disconnected_control import A_EDGES, N, adjacency
from nonbip_connected_signed_matching_exchange_q4 import (
    is_sign_changing_single_cycle,
    permutation_sign,
)


def main() -> None:
    neighbors = adjacency(A_EDGES)
    matchings: list[tuple[int, ...]] = []

    def visit(row: int, used: set[int], prefix: list[int]) -> None:
        if row == N:
            matchings.append(tuple(prefix))
            return
        for column in sorted(neighbors[row] - used):
            visit(row + 1, used | {column}, prefix + [column])

    visit(0, set(), [])
    index = {matching: i for i, matching in enumerate(matchings)}

    triangle_graph = nx.Graph()
    triangle_graph.add_nodes_from(range(len(matchings)))
    for matching_index, matching in enumerate(matchings):
        # A directed 3-cycle i->j->k->i in the matching-contracted graph is
        # exactly a Levi alternating 6-cycle, hence a sign-preserving flip.
        for i in range(N):
            for j in range(i + 1, N):
                for k in range(j + 1, N):
                    for cycle in ((i, j, k), (i, k, j)):
                        a, b, c = cycle
                        if (
                            matching[b] in neighbors[a]
                            and matching[c] in neighbors[b]
                            and matching[a] in neighbors[c]
                        ):
                            switched = list(matching)
                            switched[a] = matching[b]
                            switched[b] = matching[c]
                            switched[c] = matching[a]
                            triangle_graph.add_edge(
                                matching_index, index[tuple(switched)]
                            )

    components = list(nx.connected_components(triangle_graph))
    component_of = {
        vertex: component_index
        for component_index, component in enumerate(components)
        for vertex in component
    }
    signs = {
        permutation_sign(matchings[next(iter(component))])
        for component in components
    }
    assert signs == {-1, 1}
    assert all(
        len({permutation_sign(matchings[i]) for i in component}) == 1
        for component in components
    )

    positive_components = [
        i for i, component in enumerate(components)
        if permutation_sign(matchings[next(iter(component))]) > 0
    ]
    negative_components = [
        i for i, component in enumerate(components)
        if permutation_sign(matchings[next(iter(component))]) < 0
    ]
    size_profile = Counter(len(component) for component in components)

    # Exact component quotient: test every opposite-sign pair.  Stop after
    # finding one witness edge for a component pair.
    quotient = nx.Graph()
    quotient.add_nodes_from(positive_components, bipartite=0)
    quotient.add_nodes_from(negative_components, bipartite=1)
    for pc in positive_components:
        for nc in negative_components:
            if any(
                is_sign_changing_single_cycle(matchings[u], matchings[v])
                for u in components[pc]
                for v in components[nc]
            ):
                quotient.add_edge(pc, nc)

    print(f"matchings={len(matchings)} triangle_edges={triangle_graph.number_of_edges()}")
    print(f"components={len(components)} positive={len(positive_components)} negative={len(negative_components)}")
    print(f"component_size_profile={dict(sorted(size_profile.items()))}")
    print(f"quotient_edges={quotient.number_of_edges()}")
    if len(positive_components) == len(negative_components):
        pairing = nx.algorithms.bipartite.maximum_matching(
            quotient, top_nodes=set(positive_components)
        )
        print(f"quotient_matching_covers={len(pairing) // 2}/{len(positive_components)}")
    else:
        print("quotient perfect matching impossible: shore component counts differ")


if __name__ == "__main__":
    main()
