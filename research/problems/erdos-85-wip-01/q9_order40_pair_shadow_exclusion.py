#!/usr/bin/env python3
"""Exclude four disconnected q=9 shadows made from two order-40 components.

The covered component ordinals are 4, 5, 6, and 7 in the PSV order-40
census.  Each doubled graph has automorphism group of order 3200.  The script
uses pynauty for the full automorphism group, asks GAP (in its Docker image)
for representatives of every conjugacy class of transitive subgroups, then
checks every invariant 80-line triple orbit.

Verified with NetworkX 3.6.1, pynauty 2.8.8.1, and GAP 4.15.1 from
gapsystem/gap-docker.
"""

from __future__ import annotations

import argparse
import hashlib
import subprocess
from collections import Counter
from itertools import combinations
from pathlib import Path

import networkx as nx
import pynauty

from q9_connected_shadow_orbit_exclusion import classify_line_orbit
from q9_vt_levi_shadow_orbit_exclusion import decode, generated_group


EXPECTED_SHA256 = "4bac89beec1465265318266117c38a2c1680e73a21efd322411207cef5313088"
COMPONENT_ORDINALS = {4, 5, 6, 7}
EXPECTED_META = {
    4: (3200, 695, 34),
    5: (3200, 695, 34),
    6: (3200, 695, 34),
    7: (3200, 695, 34),
}


def cycle_notation(permutation: list[int]) -> str:
    seen = set()
    cycles = []
    for start in range(len(permutation)):
        if start in seen or permutation[start] == start:
            continue
        cycle = []
        vertex = start
        while vertex not in seen:
            seen.add(vertex)
            cycle.append(vertex + 1)
            vertex = permutation[vertex]
        cycles.append("(" + ",".join(map(str, cycle)) + ")")
    return "".join(cycles) or "()"


def gap_transitive_representatives(
    generators: list[list[int]],
) -> tuple[tuple[int, int, int], list[tuple[int, int, list[tuple[int, ...]]]]]:
    encoded_group = ",".join(cycle_notation(generator) for generator in generators)
    gap_code = f"""
SizeScreen([100000,100000]);;
G:=Group([{encoded_group}]);;
classes:=ConjugacyClassesSubgroups(G);;
trans:=Filtered(classes,c->IsTransitive(Representative(c),[1..80]));;
Print("META|",Size(G),"|",Length(classes),"|",Length(trans),"\\n");;
for c in trans do
  H:=Representative(c);;
  Print("H|",Size(H),"|",Size(c),"|");;
  first:=true;;
  for gen in GeneratorsOfGroup(H) do
    if not first then Print(";"); fi;;
    first:=false;;
    Print(JoinStringsWithSeparator(List([1..80],i->String(i^gen)),","));;
  od;;
  Print("\\n");;
od;;
QUIT;
"""
    process = subprocess.run(
        ["docker", "run", "--rm", "-i", "gapsystem/gap-docker", "gap", "-q"],
        input=gap_code,
        text=True,
        capture_output=True,
        check=True,
    )
    lines = [line.strip() for line in process.stdout.splitlines() if line.strip()]
    tag, order, class_count, transitive_count = lines[0].split("|")
    assert tag == "META"
    meta = (int(order), int(class_count), int(transitive_count))
    representatives = []
    for line in lines[1:]:
        tag, subgroup_order, class_size, encoded_generators = line.split("|")
        assert tag == "H"
        subgroup_generators = [
            tuple(int(image) - 1 for image in generator.split(","))
            for generator in encoded_generators.split(";")
        ]
        representatives.append(
            (int(subgroup_order), int(class_size), subgroup_generators)
        )
    assert len(representatives) == meta[2]
    return meta, representatives


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
        if component_ordinal not in COMPONENT_ORDINALS:
            continue
        seen_ordinals.add(component_ordinal)
        shadow = nx.disjoint_union(component, component)

        generators, size_base, size_exponent, _, orbit_count = pynauty.autgrp(
            pynauty.Graph(
                80, adjacency_dict={vertex: list(shadow[vertex]) for vertex in shadow}
            )
        )
        assert int(size_base * (10**size_exponent)) == 3200
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
        for subgroup_order, class_size, subgroup_generators in representatives:
            assert all(len(generator) == 80 for generator in subgroup_generators)
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
                # In all four classifications, there is no orbit below size
                # 80.  Hence an invariant 80-line set is one size-80 orbit.
                assert len(orbit) >= 80
                if len(orbit) == 80:
                    outcomes[classify_line_orbit(shadow, orbit)] += 1

            assert outcomes["witness"] == 0
            representative_line_orbits += sum(outcomes.values())
            for outcome, count in outcomes.items():
                weighted_outcomes[outcome] += class_size * count

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

    assert seen_ordinals == COMPONENT_ORDINALS
    print("excluded_order40_pair_shadow_types 4")


if __name__ == "__main__":
    main()
