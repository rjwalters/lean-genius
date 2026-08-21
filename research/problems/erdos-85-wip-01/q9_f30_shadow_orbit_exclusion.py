#!/usr/bin/env python3
"""Verify the five transitive-subgroup classes for CubicVT[80,30].

First run q9_f30_transitive_subgroups.g with GAP and save its six output lines.
This verifier checks those subgroup representatives against the pinned PSV
census graph, enumerates every invariant 80-line orbit, and excludes it.

Example:

  gap -q q9_f30_transitive_subgroups.g > /tmp/f30-subgroups.txt
  python3 q9_f30_shadow_orbit_exclusion.py \
      cubicvt4-300g6.txt /tmp/f30-subgroups.txt
"""

from __future__ import annotations

import argparse
import hashlib
from collections import Counter
from itertools import combinations
from pathlib import Path

import networkx as nx

from q9_connected_shadow_orbit_exclusion import classify_line_orbit
from q9_vt_levi_shadow_orbit_exclusion import decode, generated_group


EXPECTED_SHA256 = "4bac89beec1465265318266117c38a2c1680e73a21efd322411207cef5313088"
EXPECTED = {
    (160, 6): Counter({"C4": 13, "nonlinear": 15, "shadow_violation": 2}),
    (240, 2): Counter({"C4": 2, "nonlinear": 7}),
    (480, 1, 0): Counter({"nonlinear": 3}),
    (480, 1, 1): Counter({"nonlinear": 3}),
    (960, 1): Counter({"nonlinear": 1}),
}


def order_80_ordinal_30(raw: bytes) -> nx.Graph:
    ordinal = 0
    for raw_line in raw.splitlines():
        encoded = raw_line.strip()
        if not encoded:
            continue
        graph = decode(encoded)
        if len(graph) != 80:
            continue
        ordinal += 1
        if ordinal == 30:
            return graph
    raise AssertionError("missing order-80 ordinal 30")


def parse_certificate(path: Path) -> list[tuple[int, int, list[tuple[int, ...]]]]:
    lines = [line.strip() for line in path.read_text().splitlines() if line.strip()]
    assert lines[0] == "META|960|132|5"
    representatives = []
    for line in lines[1:]:
        tag, order, class_size, encoded_generators = line.split("|")
        assert tag == "H"
        generators = [
            tuple(int(image) - 1 for image in generator.split(","))
            for generator in encoded_generators.split(";")
        ]
        assert all(len(generator) == 80 for generator in generators)
        representatives.append((int(order), int(class_size), generators))
    assert len(representatives) == 5
    assert Counter((order, class_size) for order, class_size, _ in representatives) == Counter(
        {(160, 6): 1, (240, 2): 1, (480, 1): 2, (960, 1): 1}
    )
    return representatives


def is_automorphism(graph: nx.Graph, permutation: tuple[int, ...]) -> bool:
    return all(
        graph.has_edge(permutation[x], permutation[y]) for x, y in graph.edges()
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("census", type=Path)
    parser.add_argument("subgroup_certificate", type=Path)
    args = parser.parse_args()
    raw = args.census.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != EXPECTED_SHA256:
        raise SystemExit(
            f"unexpected census SHA-256: {digest}; expected {EXPECTED_SHA256}"
        )
    shadow = order_80_ordinal_30(raw)
    representatives = parse_certificate(args.subgroup_certificate)

    distance_two = dict(nx.all_pairs_shortest_path_length(shadow, cutoff=2))
    allowed_triples = {
        triple
        for triple in combinations(range(80), 3)
        if all(y not in distance_two[x] for x, y in combinations(triple, 2))
    }
    assert len(allowed_triples) == 56_640

    seen_480 = 0
    total_line_orbits = 0
    for order, class_size, generators in representatives:
        assert all(is_automorphism(shadow, generator) for generator in generators)
        subgroup = generated_group([list(generator) for generator in generators], 80)
        assert len(subgroup) == order
        assert {permutation[0] for permutation in subgroup} == set(range(80))

        unseen = set(allowed_triples)
        outcomes = Counter()
        orbit_sizes = Counter()
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
            orbit_sizes[len(orbit)] += 1
            assert len(orbit) >= 80
            if len(orbit) == 80:
                outcomes[classify_line_orbit(shadow, orbit)] += 1

        key: tuple[int, ...]
        if order == 480:
            key = (order, class_size, seen_480)
            seen_480 += 1
        else:
            key = (order, class_size)
        assert outcomes == EXPECTED[key], (key, outcomes, EXPECTED[key])
        assert outcomes["witness"] == 0
        line_orbits = sum(outcomes.values())
        total_line_orbits += class_size * line_orbits
        print(
            f"order={order}",
            f"conjugates={class_size}",
            f"orbit_sizes={dict(sorted(orbit_sizes.items()))}",
            f"line_orbits={line_orbits}",
            f"outcomes={dict(outcomes)}",
            "witnesses=0",
        )

    # There are 11 actual transitive subgroups across the five conjugacy
    # classes; conjugation preserves every tested graph property.
    assert sum(class_size for _, class_size, _ in representatives) == 11
    assert total_line_orbits == 6 * 30 + 2 * 9 + 3 + 3 + 1
    print("excluded_connected_shadow_ordinal 30")
    print("excluded_connected_shadow_types_total 25")


if __name__ == "__main__":
    main()
