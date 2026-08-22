#!/usr/bin/env python3
"""Internal 2-factor sieve for the final order-40-pair q=9 shadow.

For component census ordinal 11, a symmetric 80_3 configuration over two
40-vertex shadow components has exactly 40 lines of block type 2+1 in each
direction.  Hence the triangular graph induced on either component is an
invariant 2-regular graph with 40 edges.

This script enumerates all transitive subgroup classes of the component
automorphism group (order 480), all eligible pair-orbital unions of valency
two, and discards those containing a 4-cycle.
"""

from __future__ import annotations

import argparse
import hashlib
from collections import Counter
from itertools import combinations
from pathlib import Path

import networkx as nx
import pynauty

from q9_order40_pair_shadow_exclusion import gap_transitive_representatives
from q9_vt_levi_shadow_orbit_exclusion import decode, generated_group


EXPECTED_SHA256 = "4bac89beec1465265318266117c38a2c1680e73a21efd322411207cef5313088"
EXPECTED_META = (480, 106, 5)
EXPECTED_ROWS = [
    (80, 6, 13, Counter({(10, 10, 10, 10): 5, (4,) * 10: 5,
                         (8, 8, 8, 8, 8): 2, (5,) * 8: 1})),
    (120, 2, 3, Counter({(4,) * 10: 3})),
    (240, 1, 1, Counter({(4,) * 10: 1})),
    (240, 1, 3, Counter({(4,) * 10: 3})),
    (480, 1, 1, Counter({(4,) * 10: 1})),
]


def component_ordinal_11(raw: bytes) -> nx.Graph:
    ordinal = 0
    for raw_line in raw.splitlines():
        encoded = raw_line.strip()
        if not encoded:
            continue
        graph = decode(encoded)
        if len(graph) != 40:
            continue
        ordinal += 1
        if ordinal == 11:
            return graph
    raise AssertionError("missing order-40 ordinal 11")


def orbital_unions_of_valency_two(
    orbits: list[set[tuple[int, int]]], degree: int
) -> list[tuple[int, ...]]:
    valencies = [2 * len(orbit) // degree for orbit in orbits]
    answers = []

    def visit(position: int, valency: int, selected: list[int]) -> None:
        if valency == 2:
            answers.append(tuple(selected))
            return
        for i in range(position, len(orbits)):
            new_valency = valency + valencies[i]
            if new_valency <= 2:
                visit(i + 1, new_valency, selected + [i])

    visit(0, 0, [])
    return answers


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
    component = component_ordinal_11(raw)
    generators, size_base, size_exponent, _, orbit_count = pynauty.autgrp(
        pynauty.Graph(
            40, adjacency_dict={vertex: list(component[vertex]) for vertex in component}
        )
    )
    assert int(size_base * (10**size_exponent)) == 480
    assert orbit_count == 1
    meta, representatives = gap_transitive_representatives(generators, degree=40)
    assert meta == EXPECTED_META

    distance_two = dict(nx.all_pairs_shortest_path_length(component, cutoff=2))
    eligible_pairs = {
        pair
        for pair in combinations(range(40), 2)
        if pair[1] not in distance_two[pair[0]]
    }
    rows = []
    surviving_cycle_types = Counter()
    for subgroup_order, class_size, subgroup_generators in representatives:
        subgroup = generated_group(
            [list(generator) for generator in subgroup_generators], 40
        )
        assert len(subgroup) == subgroup_order
        assert {permutation[0] for permutation in subgroup} == set(range(40))

        unseen = set(eligible_pairs)
        orbits = []
        while unseen:
            pair = min(unseen)
            orbit = {
                tuple(sorted((permutation[pair[0]], permutation[pair[1]])))
                for permutation in subgroup
            }
            assert orbit <= eligible_pairs
            unseen -= orbit
            orbits.append(orbit)

        cycle_types = Counter()
        unions = orbital_unions_of_valency_two(orbits, 40)
        for selected in unions:
            internal = nx.Graph()
            internal.add_nodes_from(range(40))
            for i in selected:
                internal.add_edges_from(orbits[i])
            assert set(dict(internal.degree()).values()) == {2}
            cycle_type = tuple(
                sorted(len(vertices) for vertices in nx.connected_components(internal))
            )
            cycle_types[cycle_type] += 1
            if 4 not in cycle_type:
                surviving_cycle_types[cycle_type] += class_size
        rows.append((subgroup_order, class_size, len(unions), cycle_types))
        print(
            f"subgroup_order={subgroup_order}",
            f"conjugates={class_size}",
            f"two_factors={len(unions)}",
            f"cycle_types={dict(cycle_types)}",
        )

    assert rows == EXPECTED_ROWS, (rows, EXPECTED_ROWS)
    assert surviving_cycle_types == Counter(
        {(10, 10, 10, 10): 30, (8, 8, 8, 8, 8): 12, (5,) * 8: 6}
    )
    print("representative_two_factors 21")
    print("representative_C4_free_two_factors 8")
    print("surviving_projection_class_order 80")


if __name__ == "__main__":
    main()
