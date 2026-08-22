#!/usr/bin/env python3
"""Internal triangular-edge sieve for the q=9 order-20x4 shadows.

The component stabilizer of a vertex-transitive lift is transitive on each
20-point shadow component.  For each surviving PSV component ordinal, this
script enumerates the transitive subgroup classes and every invariant union
of eligible internal pair orbitals.  An eligible pair has shadow distance at
least three; each union is then tested against the intrinsic shadow-edge
condition and C4-freeness.
"""

from __future__ import annotations

import argparse
import hashlib
from collections import Counter
from itertools import combinations
from pathlib import Path

import networkx as nx
import pynauty

from q9_connected_shadow_orbit_exclusion import contains_c4
from q9_order40_pair_shadow_exclusion import gap_transitive_representatives
from q9_vt_levi_shadow_orbit_exclusion import decode, generated_group


EXPECTED_SHA256 = "4bac89beec1465265318266117c38a2c1680e73a21efd322411207cef5313088"
ORDINALS = (4, 6, 7)
EXPECTED_RESULTS = {
    4: ((20, 10, 1), 20, {"survivor": 1, "C4": 149, "shadow_violation": 362}),
    6: ((120, 22, 2), 120, {"survivor": 2, "C4": 8, "shadow_violation": 14}),
    7: ((240, 57, 4), 240, {"survivor": 9, "C4": 78, "shadow_violation": 129}),
}


def components(raw: bytes) -> dict[int, nx.Graph]:
    ordinal = 0
    result = {}
    for raw_line in raw.splitlines():
        encoded = raw_line.strip()
        if not encoded:
            continue
        graph = decode(encoded)
        if len(graph) != 20:
            continue
        ordinal += 1
        if ordinal in ORDINALS:
            result[ordinal] = graph
    assert set(result) == set(ORDINALS)
    return result


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

    grand_outcomes = Counter()
    for ordinal, component in components(raw).items():
        generators, size_base, size_exponent, _, orbit_count = pynauty.autgrp(
            pynauty.Graph(
                20,
                adjacency_dict={
                    vertex: list(component[vertex]) for vertex in component
                },
            )
        )
        automorphism_order = int(size_base * (10**size_exponent))
        assert orbit_count == 1
        meta, representatives = gap_transitive_representatives(
            generators, degree=20
        )

        distance_two = dict(nx.all_pairs_shortest_path_length(component, cutoff=2))
        eligible_pairs = {
            pair
            for pair in combinations(range(20), 2)
            if pair[1] not in distance_two[pair[0]]
        }
        weighted_outcomes = Counter()
        survivor_profiles = Counter()
        for subgroup_order, class_size, subgroup_generators in representatives:
            subgroup = generated_group(
                [list(generator) for generator in subgroup_generators], 20
            )
            assert len(subgroup) == subgroup_order
            assert {permutation[0] for permutation in subgroup} == set(range(20))

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

            outcomes = Counter()
            for mask in range(1 << len(orbits)):
                internal = nx.Graph()
                internal.add_nodes_from(range(20))
                for index, orbit in enumerate(orbits):
                    if (mask >> index) & 1:
                        internal.add_edges_from(orbit)
                combined = nx.compose(component, internal)
                if any(
                    set(combined[x]) & set(combined[y])
                    for x, y in component.edges()
                ):
                    outcomes["shadow_violation"] += 1
                elif contains_c4(combined):
                    outcomes["C4"] += 1
                else:
                    outcomes["survivor"] += 1
                    degree = internal.degree[0]
                    assert all(internal.degree[v] == degree for v in internal)
                    survivor_profiles[(subgroup_order, degree)] += class_size

            for outcome, count in outcomes.items():
                weighted_outcomes[outcome] += class_size * count

        grand_outcomes.update(weighted_outcomes)
        expected_meta, expected_automorphism_order, expected_outcomes = (
            EXPECTED_RESULTS[ordinal]
        )
        assert meta == expected_meta
        assert automorphism_order == expected_automorphism_order
        assert dict(weighted_outcomes) == expected_outcomes
        assert all(degree == 0 for _, degree in survivor_profiles)
        assert sum(survivor_profiles.values()) == weighted_outcomes["survivor"]
        print(
            f"ordinal={ordinal}",
            f"automorphism_order={automorphism_order}",
            f"subgroup_meta={meta}",
            f"eligible_pairs={len(eligible_pairs)}",
            f"outcomes={dict(weighted_outcomes)}",
            f"survivor_profiles={dict(survivor_profiles)}",
        )
    print(f"grand_outcomes={dict(grand_outcomes)}")
    # With no internal edge, every configuration line meets three distinct
    # components.  If w_i is the number of lines omitting block i, then each
    # block lies on 20 * 3 = 60 lines and there are 80 lines in total, so
    # w_i = 80 - 60 = 20 for all four blocks.
    print("internal_triangular_edges 0")
    print("configuration_line_component_type 1+1+1")
    print("block_triple_weights 20 20 20 20")


if __name__ == "__main__":
    main()
