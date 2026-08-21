#!/usr/bin/env python3
"""Exclude every vertex-transitive completion of 17 q=9 Levi candidates.

This consumes the pinned PSV census used by q9_configuration_levi_census.py.
For each of the 17 cubic vertex-transitive Levi graphs of order 160 and girth
10, it constructs the 80-point triangular graph T and uses pynauty to compute
Aut(T).  It then:

* enumerates every transitive subgroup H <= Aut(T);
* partitions the eligible pairs (nonedges of T with no common T-neighbor)
  into H-orbits;
* enumerates every union of orbitals of valency three; and
* checks C4-freeness of T union F.

If a vertex-transitive q=9 graph G had this T, its automorphism group would
preserve triangle-free edges and triangular edges.  Thus Aut(G) would be one
of the transitive subgroups H checked here, and its cubic shadow F would be an
H-invariant union of eligible pair orbits.  Zero surviving unions therefore
exclude the whole 17-member vertex-transitive-Levi family.

Verified with NetworkX 3.6.1 and pynauty 2.8.8.1.
"""

from __future__ import annotations

import argparse
import hashlib
from collections import Counter
from itertools import combinations
from pathlib import Path

import networkx as nx
import pynauty


EXPECTED_SHA256 = "4bac89beec1465265318266117c38a2c1680e73a21efd322411207cef5313088"
LEVI_ORDINALS = {41, 42, 43, 44, 53, 56, 62, 63, 64, 66, 75, 76, 80, 84, 100, 101, 104}
EXPECTED_UNION_COUNTS = {
    41: [24],
    42: [24],
    43: [24],
    44: [24],
    53: [182],
    56: [70],
    62: [70],
    63: [70],
    64: [70],
    66: [70],
    75: [120],
    76: [120],
    80: [120],
    84: [24],
    100: [4, 24, 24],
    101: [22, 70, 70],
    104: [22, 70, 70],
}
EXPECTED_SUBGROUP_COUNTS = {100: 68, 101: 172, 104: 188}


Permutation = tuple[int, ...]


def decode(line: bytes) -> nx.Graph:
    return (
        nx.from_sparse6_bytes(line)
        if line.startswith(b":")
        else nx.from_graph6_bytes(line)
    )


def compose(left: Permutation, right: Permutation) -> Permutation:
    return tuple(left[right[i]] for i in range(len(left)))


def generated_group(generators: list[list[int]], degree: int) -> list[Permutation]:
    identity = tuple(range(degree))
    generators = [tuple(generator) for generator in generators]
    group = {identity}
    pending = [identity]
    while pending:
        element = pending.pop()
        for generator in generators:
            product = compose(generator, element)
            if product not in group:
                group.add(product)
                pending.append(product)
    return sorted(group)


def all_transitive_subgroups(
    group: list[Permutation], degree: int
) -> tuple[int, list[frozenset[int]]]:
    """Enumerate the subgroup lattice by adjoining every outside element."""
    index = {element: i for i, element in enumerate(group)}
    identity = index[tuple(range(degree))]
    multiplication = [
        [index[compose(left, right)] for right in group] for left in group
    ]
    inverse = [
        next(j for j in range(len(group)) if multiplication[i][j] == identity)
        for i in range(len(group))
    ]

    def closure(generators: tuple[int, ...]) -> frozenset[int]:
        symmetric_generators = set(generators)
        symmetric_generators.update(inverse[g] for g in generators)
        subgroup = {identity}
        pending = [identity]
        while pending:
            element = pending.pop()
            for generator in symmetric_generators:
                product = multiplication[generator][element]
                if product not in subgroup:
                    subgroup.add(product)
                    pending.append(product)
        return frozenset(subgroup)

    trivial = frozenset({identity})
    generators_for = {trivial: ()}
    pending = [trivial]
    while pending:
        subgroup = pending.pop()
        old_generators = generators_for[subgroup]
        # Every outside element is essential here: collapsing all elements of
        # <H,g> can skip a proper intermediate subgroup <H,h>.
        for element in range(len(group)):
            if element in subgroup:
                continue
            extension = closure(old_generators + (element,))
            if extension not in generators_for:
                generators_for[extension] = old_generators + (element,)
                pending.append(extension)

    transitive = [
        subgroup
        for subgroup in generators_for
        if len({group[element][0] for element in subgroup}) == degree
    ]
    return len(generators_for), transitive


def point_graph(levi: nx.Graph) -> nx.Graph:
    points, lines = nx.bipartite.sets(levi)
    points = sorted(points)
    point_index = {point: i for i, point in enumerate(points)}
    triangular = nx.Graph()
    triangular.add_nodes_from(range(80))
    for line in lines:
        triangular.add_edges_from(
            combinations([point_index[point] for point in levi[line]], 2)
        )
    return triangular


def orbit_unions_of_valency_three(
    orbits: list[set[tuple[int, int]]]
) -> list[tuple[int, ...]]:
    valencies = [2 * len(orbit) // 80 for orbit in orbits]
    answers = []

    def visit(position: int, valency: int, selected: list[int]) -> None:
        if valency == 3:
            answers.append(tuple(selected))
            return
        for i in range(position, len(orbits)):
            new_valency = valency + valencies[i]
            if new_valency <= 3:
                visit(i + 1, new_valency, selected + [i])

    visit(0, 0, [])
    return answers


def check_transitive_group(
    triangular: nx.Graph,
    group: list[Permutation],
    subgroup: frozenset[int],
) -> tuple[int, int]:
    eligible = {
        pair
        for pair in combinations(range(80), 2)
        if not triangular.has_edge(*pair)
        and len(nx.common_neighbors(triangular, *pair)) == 0
    }
    assert len(eligible) == 1_960  # the compatibility graph is 49-regular

    permutations = [group[element] for element in subgroup]
    unseen = set(eligible)
    orbits = []
    while unseen:
        pair = min(unseen)
        orbit = {
            tuple(sorted((permutation[pair[0]], permutation[pair[1]])))
            for permutation in permutations
        }
        assert orbit <= eligible
        unseen -= orbit
        orbits.append(orbit)

    unions = orbit_unions_of_valency_three(orbits)
    minimum_maximum_common = 80
    witnesses = 0
    for selected in unions:
        shadow = nx.Graph()
        shadow.add_nodes_from(range(80))
        for i in selected:
            shadow.add_edges_from(orbits[i])
        assert set(dict(shadow.degree()).values()) == {3}
        candidate = nx.compose(triangular, shadow)
        maximum_common = max(
            len(nx.common_neighbors(candidate, x, y))
            for x, y in combinations(range(80), 2)
        )
        minimum_maximum_common = min(minimum_maximum_common, maximum_common)
        if maximum_common <= 1:
            witnesses += 1
    assert witnesses == 0
    assert minimum_maximum_common >= 2
    return len(unions), witnesses


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("census", type=Path)
    args = parser.parse_args()
    raw = args.census.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != EXPECTED_SHA256:
        raise SystemExit(
            f"unexpected census SHA-256: {digest}; expected {EXPECTED_SHA256}"
        )

    ordinal = 0
    seen_ordinals = set()
    for raw_line in raw.splitlines():
        encoded = raw_line.strip()
        if not encoded:
            continue
        levi = decode(encoded)
        if len(levi) != 160:
            continue
        ordinal += 1
        if ordinal not in LEVI_ORDINALS:
            continue
        seen_ordinals.add(ordinal)
        triangular = point_graph(levi)
        nauty_graph = pynauty.Graph(
            80, adjacency_dict={vertex: list(triangular[vertex]) for vertex in triangular}
        )
        generators, size_base, size_exponent, _, orbit_count = pynauty.autgrp(
            nauty_graph
        )
        automorphism_group = generated_group(generators, 80)
        nauty_size = int(size_base * (10**size_exponent))
        assert len(automorphism_group) == nauty_size
        assert orbit_count == 1

        if len(automorphism_group) == 80:
            # A transitive subgroup has order divisible by 80, so a regular
            # automorphism group of order 80 has no proper transitive subgroup.
            transitive_subgroups = [frozenset(range(80))]
            subgroup_count = None
        else:
            assert len(automorphism_group) == 160
            subgroup_count, transitive_subgroups = all_transitive_subgroups(
                automorphism_group, 80
            )
            assert subgroup_count == EXPECTED_SUBGROUP_COUNTS[ordinal]
            assert Counter(map(len, transitive_subgroups)) == Counter({80: 2, 160: 1})

        union_counts = []
        for subgroup in transitive_subgroups:
            union_count, witnesses = check_transitive_group(
                triangular, automorphism_group, subgroup
            )
            assert witnesses == 0
            union_counts.append(union_count)
        union_counts.sort()
        assert union_counts == EXPECTED_UNION_COUNTS[ordinal]
        print(
            f"ordinal={ordinal}",
            f"aut={len(automorphism_group)}",
            f"transitive_subgroups={len(transitive_subgroups)}",
            f"cubic_orbit_unions={','.join(map(str, union_counts))}",
            "witnesses=0",
        )

    assert seen_ordinals == LEVI_ORDINALS
    print("excluded_vertex_transitive_levi_candidates 17")


if __name__ == "__main__":
    main()
