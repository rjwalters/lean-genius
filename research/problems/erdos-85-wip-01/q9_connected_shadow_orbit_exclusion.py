#!/usr/bin/env python3
"""Exclude 24 of the 25 connected q=9 cubic-shadow types.

For every surviving connected order-80 shadow F except census ordinal 30
(whose automorphism group has order 960), this script computes every
transitive subgroup H <= Aut(F).  A candidate's 80 configuration lines form
an H-invariant set of triples.  In these 24 cases every allowed triple orbit
has size at least 80, so an invariant 80-line set must be one orbit of size
exactly 80.  Every such orbit is checked for linearity, the intrinsic
triangle-free-edge condition, and C4-freeness of the union graph.

The helper module q9_vt_levi_shadow_orbit_exclusion.py supplies the audited
finite-group closure and complete subgroup-lattice enumeration.  Verified
with NetworkX 3.6.1 and pynauty 2.8.8.1.
"""

from __future__ import annotations

import argparse
import hashlib
from collections import Counter
from itertools import combinations
from pathlib import Path

import networkx as nx
import pynauty

from q9_vt_levi_shadow_orbit_exclusion import (
    all_transitive_subgroups,
    decode,
    generated_group,
)


EXPECTED_SHA256 = "4bac89beec1465265318266117c38a2c1680e73a21efd322411207cef5313088"
SHADOW_ORDINALS = {
    2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19,
    20, 21, 23, 24, 28, 29, 32, 33,
}
# aut order, number of transitive subgroups, nonlinear, shadow violation, C4
EXPECTED = {
    2: (160, 5, 2025, 186, 674),
    3: (160, 5, 1643, 244, 977),
    4: (160, 5, 1497, 272, 1095),
    5: (160, 5, 1929, 190, 766),
    6: (160, 5, 1633, 200, 1028),
    8: (80, 1, 587, 0, 120),
    9: (80, 1, 588, 0, 118),
    10: (80, 1, 587, 0, 120),
    11: (80, 1, 587, 0, 120),
    12: (80, 1, 587, 0, 120),
    14: (80, 1, 587, 0, 120),
    15: (160, 5, 1867, 182, 822),
    16: (160, 5, 1711, 250, 898),
    17: (80, 1, 587, 0, 120),
    18: (80, 1, 587, 0, 120),
    19: (160, 5, 1871, 180, 808),
    20: (80, 1, 285, 146, 277),
    21: (80, 1, 285, 150, 273),
    23: (80, 1, 613, 0, 94),
    24: (80, 1, 611, 0, 96),
    28: (80, 1, 593, 0, 115),
    29: (160, 2, 404, 124, 206),
    32: (160, 1, 31, 1, 10),
    33: (160, 1, 19, 2, 9),
}


def contains_c4(graph: nx.Graph) -> bool:
    """Detect two distinct common neighbors by enumerating centered cherries."""
    seen_endpoint_pairs = set()
    for center in graph:
        for endpoints in combinations(sorted(graph[center]), 2):
            if endpoints in seen_endpoint_pairs:
                return True
            seen_endpoint_pairs.add(endpoints)
    return False


def classify_line_orbit(
    shadow: nx.Graph, lines: set[tuple[int, int, int]]
) -> str:
    pair_counts = Counter(
        pair for line in lines for pair in combinations(line, 2)
    )
    if max(pair_counts.values()) > 1:
        return "nonlinear"

    triangular = nx.Graph()
    triangular.add_nodes_from(range(80))
    for line in lines:
        triangular.add_edges_from(combinations(line, 2))
    assert set(dict(triangular.degree()).values()) == {6}
    candidate = nx.compose(shadow, triangular)

    if any(
        set(candidate[x]) & set(candidate[y]) for x, y in shadow.edges()
    ):
        return "shadow_violation"
    if contains_c4(candidate):
        return "C4"
    return "witness"


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
        shadow = decode(encoded)
        if len(shadow) != 80:
            continue
        ordinal += 1
        if ordinal not in SHADOW_ORDINALS:
            continue
        seen_ordinals.add(ordinal)

        generators, size_base, size_exponent, _, orbit_count = pynauty.autgrp(
            pynauty.Graph(
                80, adjacency_dict={vertex: list(shadow[vertex]) for vertex in shadow}
            )
        )
        automorphism_group = generated_group(generators, 80)
        assert len(automorphism_group) == int(size_base * (10**size_exponent))
        assert orbit_count == 1
        if len(automorphism_group) == 80:
            transitive_subgroups = [frozenset(range(80))]
        else:
            assert len(automorphism_group) == 160
            _, transitive_subgroups = all_transitive_subgroups(
                automorphism_group, 80
            )

        distance_two = dict(nx.all_pairs_shortest_path_length(shadow, cutoff=2))
        allowed_triples = {
            triple
            for triple in combinations(range(80), 3)
            if all(
                y not in distance_two[x] for x, y in combinations(triple, 2)
            )
        }

        outcomes = Counter()
        checked_orbits = 0
        for subgroup in transitive_subgroups:
            permutations = [automorphism_group[element] for element in subgroup]
            unseen = set(allowed_triples)
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
                    for permutation in permutations
                }
                assert orbit <= allowed_triples
                unseen -= orbit
                # No orbit smaller than 80 occurs.  Larger orbits cannot be a
                # subset of an invariant line set having exactly 80 members.
                assert len(orbit) >= 80
                if len(orbit) > 80:
                    continue
                checked_orbits += 1
                outcomes[classify_line_orbit(shadow, orbit)] += 1

        assert outcomes["witness"] == 0
        actual = (
            len(automorphism_group),
            len(transitive_subgroups),
            outcomes["nonlinear"],
            outcomes["shadow_violation"],
            outcomes["C4"],
        )
        assert actual == EXPECTED[ordinal], (ordinal, actual, EXPECTED[ordinal])
        assert checked_orbits == sum(outcomes.values())
        print(
            f"ordinal={ordinal}",
            f"aut={len(automorphism_group)}",
            f"transitive_subgroups={len(transitive_subgroups)}",
            f"line_orbits={checked_orbits}",
            f"nonlinear={outcomes['nonlinear']}",
            f"shadow_violation={outcomes['shadow_violation']}",
            f"C4={outcomes['C4']}",
            "witnesses=0",
        )

    assert seen_ordinals == SHADOW_ORDINALS
    print("excluded_connected_shadow_types 24")
    print("remaining_connected_shadow_ordinal 30")


if __name__ == "__main__":
    main()
