#!/usr/bin/env python3
"""Exclude the two order-12,800 automorphism-group 40+40 shadows.

This is the high-symmetry companion to q9_order40_pair_shadow_exclusion.py.
It covers order-40 component ordinals 3 and 8.  GAP enumerates 23,183 subgroup
conjugacy classes in each wreath automorphism group; 468 and 364 classes,
respectively, are transitive.  Every invariant 80-line orbit is checked.
"""

from __future__ import annotations

import argparse
import hashlib
from collections import Counter
from itertools import combinations
from pathlib import Path

import networkx as nx
import pynauty

from q9_connected_shadow_orbit_exclusion import classify_line_orbit
from q9_order40_pair_shadow_exclusion import gap_transitive_representatives
from q9_vt_levi_shadow_orbit_exclusion import decode, generated_group


EXPECTED_SHA256 = "4bac89beec1465265318266117c38a2c1680e73a21efd322411207cef5313088"
EXPECTED_META = {
    3: (12_800, 23_183, 468),
    8: (12_800, 23_183, 364),
}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("census", type=Path)
    parser.add_argument(
        "--component-ordinal",
        type=int,
        action="append",
        choices=sorted(EXPECTED_META),
        help="run one leaf; may be repeated (default: both)",
    )
    args = parser.parse_args()
    selected = set(args.component_ordinal or EXPECTED_META)
    raw = args.census.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != EXPECTED_SHA256:
        raise SystemExit(
            f"unexpected census SHA-256: {digest}; expected {EXPECTED_SHA256}"
        )

    component_ordinal = 0
    seen_ordinals = set()
    for raw_line in raw.splitlines():
        encoded = raw_line.strip()
        if not encoded:
            continue
        component = decode(encoded)
        if len(component) != 40:
            continue
        component_ordinal += 1
        if component_ordinal not in selected:
            continue
        seen_ordinals.add(component_ordinal)
        shadow = nx.disjoint_union(component, component)
        generators, size_base, size_exponent, _, orbit_count = pynauty.autgrp(
            pynauty.Graph(
                80, adjacency_dict={vertex: list(shadow[vertex]) for vertex in shadow}
            )
        )
        assert int(size_base * (10**size_exponent)) == 12_800
        assert orbit_count == 1
        meta, representatives = gap_transitive_representatives(generators)
        assert meta == EXPECTED_META[component_ordinal]

        distance_two = dict(nx.all_pairs_shortest_path_length(shadow, cutoff=2))
        allowed_triples = {
            triple
            for triple in combinations(range(80), 3)
            if all(
                y not in distance_two[x] for x, y in combinations(triple, 2)
            )
        }
        weighted_outcomes = Counter()
        representative_line_orbits = 0
        actual_transitive_subgroups = 0
        for representative_index, (
            subgroup_order,
            class_size,
            subgroup_generators,
        ) in enumerate(representatives, start=1):
            subgroup = generated_group(
                [list(generator) for generator in subgroup_generators], 80
            )
            assert len(subgroup) == subgroup_order
            assert {permutation[0] for permutation in subgroup} == set(range(80))
            actual_transitive_subgroups += class_size

            unseen = set(allowed_triples)
            outcomes = Counter()
            while unseen:
                representative = min(unseen)
                orbit = {
                    tuple(
                        sorted(
                            (
                                permutation[representative[0]],
                                permutation[representative[1]],
                                permutation[representative[2]],
                            )
                        )
                    )
                    for permutation in subgroup
                }
                assert orbit <= allowed_triples
                unseen -= orbit
                assert len(orbit) >= 80
                if len(orbit) == 80:
                    outcomes[classify_line_orbit(shadow, orbit)] += 1
            assert outcomes["witness"] == 0
            representative_line_orbits += sum(outcomes.values())
            for outcome, count in outcomes.items():
                weighted_outcomes[outcome] += class_size * count
            if representative_index % 50 == 0:
                print(
                    f"component_ordinal={component_ordinal}",
                    f"progress={representative_index}/{len(representatives)}",
                    flush=True,
                )

        assert weighted_outcomes["witness"] == 0
        print(
            f"component_ordinal={component_ordinal}",
            f"subgroup_classes={meta[1]}",
            f"transitive_classes={meta[2]}",
            f"transitive_subgroups={actual_transitive_subgroups}",
            f"representative_line_orbits={representative_line_orbits}",
            f"weighted_outcomes={dict(weighted_outcomes)}",
            "witnesses=0",
            flush=True,
        )

    assert seen_ordinals == selected
    print("excluded_highsymmetry_order40_pair_shadow_types", len(selected))


if __name__ == "__main__":
    main()
