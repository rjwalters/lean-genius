#!/usr/bin/env python3
"""Prove the q=9 order-16x5 shadow has no internal triangular edges.

The stabilizer of any connected shadow component is transitive on its 16
vertices.  This verifier enumerates every transitive subgroup class of the
component automorphism group (order 96) and every invariant union of eligible
internal pair orbitals.  The only union compatible with the intrinsic shadow
condition and C4-freeness is the empty graph.
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
EXPECTED_META = (96, 42, 8)


def component_ordinal_4(raw: bytes) -> nx.Graph:
    ordinal = 0
    for raw_line in raw.splitlines():
        encoded = raw_line.strip()
        if not encoded:
            continue
        graph = decode(encoded)
        if len(graph) != 16:
            continue
        ordinal += 1
        if ordinal == 4:
            return graph
    raise AssertionError("missing order-16 ordinal 4")


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
    component = component_ordinal_4(raw)
    generators, size_base, size_exponent, _, orbit_count = pynauty.autgrp(
        pynauty.Graph(
            16, adjacency_dict={vertex: list(component[vertex]) for vertex in component}
        )
    )
    assert int(size_base * (10**size_exponent)) == 96
    assert orbit_count == 1
    meta, representatives = gap_transitive_representatives(generators, degree=16)
    assert meta == EXPECTED_META

    distance_two = dict(nx.all_pairs_shortest_path_length(component, cutoff=2))
    eligible_pairs = {
        pair
        for pair in combinations(range(16), 2)
        if pair[1] not in distance_two[pair[0]]
    }
    assert len(eligible_pairs) == 48

    weighted_outcomes = Counter()
    for subgroup_order, class_size, subgroup_generators in representatives:
        subgroup = generated_group(
            [list(generator) for generator in subgroup_generators], 16
        )
        assert len(subgroup) == subgroup_order
        assert {permutation[0] for permutation in subgroup} == set(range(16))

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
            internal.add_nodes_from(range(16))
            for i, orbit in enumerate(orbits):
                if (mask >> i) & 1:
                    internal.add_edges_from(orbit)
            candidate_inside_component = nx.compose(component, internal)
            if any(
                set(candidate_inside_component[x]) & set(candidate_inside_component[y])
                for x, y in component.edges()
            ):
                outcomes["shadow_violation"] += 1
            elif contains_c4(candidate_inside_component):
                outcomes["C4"] += 1
            elif internal.number_of_edges() == 0:
                outcomes["empty"] += 1
            else:
                outcomes["nonempty_witness"] += 1

        assert outcomes["empty"] == 1
        assert outcomes["nonempty_witness"] == 0
        for outcome, count in outcomes.items():
            weighted_outcomes[outcome] += class_size * count
        print(
            f"subgroup_order={subgroup_order}",
            f"conjugates={class_size}",
            f"eligible_pair_orbits={len(orbits)}",
            f"outcomes={dict(outcomes)}",
        )

    assert weighted_outcomes["nonempty_witness"] == 0
    print(f"weighted_outcomes={dict(weighted_outcomes)}")
    print("internal_triangular_edges 0")
    print("configuration_line_component_type 1+1+1")


if __name__ == "__main__":
    main()
