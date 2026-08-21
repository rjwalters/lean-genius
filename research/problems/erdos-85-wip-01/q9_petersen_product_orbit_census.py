#!/usr/bin/env python3
"""Exclude nine product-symmetric q=9 configurations over Petersen^8.

The cubic shadow is eight disjoint Petersen graphs.  We test product actions
K x L, where K is F20, A5, or S5 on the Petersen vertices (the 2-subsets of
five points), and L is C8, C4 x C2, or C2^3 acting regularly on the eight
components.  Each product action is transitive on all 80 vertices.

An invariant symmetric 80_3 configuration is a union of line-triple orbits.
Point transitivity says an orbit union with three lines through each point has
exactly 80 triples.  The verifier enumerates only triple orbits of size at most
80, then checks point degree, linearity, the triangle-free-edge definition,
and C4-freeness of the resulting 9-regular graph.

This excludes these nine product actions only; it does not classify arbitrary
transitive subgroups of Aut(Petersen wr 8).
"""

from __future__ import annotations

from collections import Counter
from itertools import combinations, permutations

import networkx as nx


EXPECTED = {
    ("F20", "C8"): (28, 16, 8, 4),
    ("F20", "C4xC2"): (28, 28, 0, 0),
    ("F20", "C2^3"): (28, 28, 0, 0),
    ("A5", "C8"): (7, 5, 2, 0),
    ("A5", "C4xC2"): (7, 7, 0, 0),
    ("A5", "C2^3"): (7, 7, 0, 0),
    ("S5", "C8"): (7, 5, 2, 0),
    ("S5", "C4xC2"): (7, 7, 0, 0),
    ("S5", "C2^3"): (7, 7, 0, 0),
}


def permutation_parity(permutation: tuple[int, ...]) -> int:
    return sum(
        permutation[i] > permutation[j]
        for i in range(len(permutation))
        for j in range(i + 1, len(permutation))
    ) % 2


def petersen_data() -> tuple[nx.Graph, dict[str, list[tuple[int, ...]]]]:
    points = list(combinations(range(5), 2))
    point_index = {point: i for i, point in enumerate(points)}
    graph = nx.Graph()
    graph.add_nodes_from(range(10))
    graph.add_edges_from(
        (i, j)
        for i, j in combinations(range(10), 2)
        if set(points[i]).isdisjoint(points[j])
    )

    def induced(permutation: tuple[int, ...]) -> tuple[int, ...]:
        return tuple(
            point_index[tuple(sorted((permutation[a], permutation[b])))]
            for a, b in points
        )

    s5_permutations = list(permutations(range(5)))
    groups = {
        "F20": [
            induced(tuple((a * x + b) % 5 for x in range(5)))
            for a in range(1, 5)
            for b in range(5)
        ],
        "A5": [
            induced(permutation)
            for permutation in s5_permutations
            if permutation_parity(permutation) == 0
        ],
        "S5": [induced(permutation) for permutation in s5_permutations],
    }
    assert {name: len(group) for name, group in groups.items()} == {
        "F20": 20,
        "A5": 60,
        "S5": 120,
    }
    return graph, groups


def component_groups() -> dict[str, list[tuple[int, ...]]]:
    return {
        "C8": [tuple((i + k) % 8 for i in range(8)) for k in range(8)],
        "C4xC2": [
            tuple(4 * (((i // 4) + b) % 2) + ((i % 4 + a) % 4) for i in range(8))
            for b in range(2)
            for a in range(4)
        ],
        "C2^3": [tuple(i ^ k for i in range(8)) for k in range(8)],
    }


def orbit_unions_of_size(
    orbits: list[tuple[tuple[int, int, int], ...]], target: int
) -> list[tuple[int, ...]]:
    answers: list[tuple[int, ...]] = []

    def visit(position: int, total: int, selected: list[int]) -> None:
        if total == target:
            answers.append(tuple(selected))
            return
        for i in range(position, len(orbits)):
            new_total = total + len(orbits[i])
            if new_total <= target:
                visit(i + 1, new_total, selected + [i])

    visit(0, 0, [])
    return answers


def main() -> None:
    petersen, internal_groups = petersen_data()
    component_actions = component_groups()
    distances = dict(nx.all_pairs_shortest_path_length(petersen))
    allowed_triples = [
        triple
        for triple in combinations(range(80), 3)
        if all(
            x // 10 != y // 10 or distances[x % 10][y % 10] >= 3
            for x, y in combinations(triple, 2)
        )
    ]
    assert len(allowed_triples) == 56_000
    shadow = nx.disjoint_union_all([petersen.copy() for _ in range(8)])

    results = {}
    for internal_name, internal_group in internal_groups.items():
        for component_name, component_group in component_actions.items():
            unseen = set(allowed_triples)
            orbits = []
            while unseen:
                representative = min(unseen)
                orbit = {
                    tuple(
                        sorted(
                            10 * component_permutation[v // 10]
                            + internal_permutation[v % 10]
                            for v in representative
                        )
                    )
                    for internal_permutation in internal_group
                    for component_permutation in component_group
                }
                unseen -= orbit
                orbits.append(tuple(sorted(orbit)))

            small_orbits = [orbit for orbit in orbits if len(orbit) <= 80]
            unions = orbit_unions_of_size(small_orbits, 80)
            nonlinear = 0
            linear_c4 = 0
            shadow_violation = 0
            witnesses = 0
            for selected in unions:
                lines = [line for i in selected for line in small_orbits[i]]
                point_counts = Counter(v for line in lines for v in line)
                pair_counts = Counter(
                    pair for line in lines for pair in combinations(line, 2)
                )
                if (
                    len(point_counts) != 80
                    or set(point_counts.values()) != {3}
                    or max(pair_counts.values()) > 1
                ):
                    nonlinear += 1
                    continue

                triangular = nx.Graph()
                triangular.add_nodes_from(range(80))
                for line in lines:
                    triangular.add_edges_from(combinations(line, 2))
                candidate = nx.compose(shadow, triangular)
                bad_shadow_edge = any(
                    nx.common_neighbors(candidate, x, y)
                    for x, y in shadow.edges()
                )
                bad_c4 = any(
                    len(nx.common_neighbors(candidate, x, y)) > 1
                    for x, y in combinations(range(80), 2)
                )
                if bad_shadow_edge:
                    shadow_violation += 1
                elif bad_c4:
                    linear_c4 += 1
                else:
                    witnesses += 1

            result = (len(unions), nonlinear, linear_c4, shadow_violation)
            results[(internal_name, component_name)] = result
            print(
                internal_name,
                component_name,
                f"unions={len(unions)}",
                f"nonlinear={nonlinear}",
                f"linear_but_C4={linear_c4}",
                f"shadow_violation={shadow_violation}",
                f"witnesses={witnesses}",
            )
            assert witnesses == 0

    assert results == EXPECTED, (results, EXPECTED)


if __name__ == "__main__":
    main()
