#!/usr/bin/env python3
"""Close the final q=9 order-40-pair shadow by a restricted wreath lift.

The internal sieve leaves only a regular order-80 component projection K.
It is unique up to six conjugates in the component automorphism group A of
order 480, hence N_A(K) has order 80 and equals K.  After independently
conjugating the two components, every remaining transitive candidate group is
therefore contained in K wr C2, of order 12,800.

This verifier enumerates every transitive subgroup class of that restricted
wreath product and every invariant 80-line triple orbit.
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
EXPECTED_COMPONENT_META = (480, 106, 5)
EXPECTED_WREATH_META = (12_800, 5_264, 75)


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


def restricted_wreath_generators(
    component_generators: list[tuple[int, ...]],
) -> list[list[int]]:
    generators = []
    for generator in component_generators:
        generators.append(list(generator) + list(range(40, 80)))
        generators.append(list(range(40)) + [image + 40 for image in generator])
    generators.append(list(range(40, 80)) + list(range(40)))
    return generators


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
    component_aut_generators, size_base, size_exponent, _, orbit_count = (
        pynauty.autgrp(
            pynauty.Graph(
                40,
                adjacency_dict={vertex: list(component[vertex]) for vertex in component},
            )
        )
    )
    assert int(size_base * (10**size_exponent)) == 480
    assert orbit_count == 1
    component_meta, component_representatives = gap_transitive_representatives(
        component_aut_generators, degree=40
    )
    assert component_meta == EXPECTED_COMPONENT_META
    regular_rows = [
        (class_size, generators)
        for order, class_size, generators in component_representatives
        if order == 80
    ]
    assert len(regular_rows) == 1
    class_size, regular_generators = regular_rows[0]
    assert class_size == 6
    regular_group = generated_group(
        [list(generator) for generator in regular_generators], 40
    )
    assert len(regular_group) == 80
    assert {permutation[0] for permutation in regular_group} == set(range(40))
    # Six conjugates in a group of order 480 give |N_A(K)| = 80 = |K|.
    assert 480 // class_size == len(regular_group)

    shadow = nx.disjoint_union(component, component)
    wreath_generators = restricted_wreath_generators(regular_generators)
    wreath_group = generated_group(wreath_generators, 80)
    assert len(wreath_group) == 12_800
    wreath_meta, representatives = gap_transitive_representatives(wreath_generators)
    assert wreath_meta == EXPECTED_WREATH_META

    distance_two = dict(nx.all_pairs_shortest_path_length(shadow, cutoff=2))
    allowed_triples = {
        triple
        for triple in combinations(range(80), 3)
        if all(y not in distance_two[x] for x, y in combinations(triple, 2))
    }
    weighted_outcomes = Counter()
    representative_line_orbits = 0
    actual_transitive_subgroups = 0
    for representative_index, (
        subgroup_order,
        subgroup_class_size,
        subgroup_generators,
    ) in enumerate(representatives, start=1):
        subgroup = generated_group(
            [list(generator) for generator in subgroup_generators], 80
        )
        assert len(subgroup) == subgroup_order
        assert {permutation[0] for permutation in subgroup} == set(range(80))
        actual_transitive_subgroups += subgroup_class_size

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
            weighted_outcomes[outcome] += subgroup_class_size * count
        if representative_index % 25 == 0:
            print(
                f"progress={representative_index}/{len(representatives)}", flush=True
            )

    assert weighted_outcomes["witness"] == 0
    print(
        f"subgroup_classes={wreath_meta[1]}",
        f"transitive_classes={wreath_meta[2]}",
        f"transitive_subgroups={actual_transitive_subgroups}",
        f"representative_line_orbits={representative_line_orbits}",
        f"weighted_outcomes={dict(weighted_outcomes)}",
        "witnesses=0",
    )
    print("excluded_order40_pair_component_ordinal 11")
    print("excluded_order40_pair_shadow_types_total 7")


if __name__ == "__main__":
    main()
