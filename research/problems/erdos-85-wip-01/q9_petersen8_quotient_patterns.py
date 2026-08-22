#!/usr/bin/env python3
"""Classify transitive component quotients for a Petersen^8 q=9 shadow.

Any triangular color on eight Petersen components induces a weighted
3-uniform hypergraph on the component set.  Point transitivity makes the
component action transitive.  There are 80 triangles, every component lies
in 30 of them, and the matching law between two Petersen blocks bounds every
pair codegree by 10.

This script checks those necessary equations for all 50 transitive groups of
degree eight in GAP's library.  It is the quotient stage of the exhaustive
Petersen^8 classification; surviving patterns still require a lift check.

Verified with GAP 4.15.1 from gapsystem/gap-docker and z3-solver 4.15.3.
"""

from __future__ import annotations

import subprocess
import hashlib
from itertools import combinations

import z3


TRIPLES = tuple(combinations(range(8), 3))
PAIRS = tuple(combinations(range(8), 2))


def gap_transitive_generators() -> list[tuple[int, int, list[tuple[int, ...]]]]:
    gap_code = r'''
SizeScreen([100000,100000]);;
Print("COUNT|",NrTransitiveGroups(8),"\n");;
for i in [1..NrTransitiveGroups(8)] do
  G:=TransitiveGroup(8,i);;
  Print("G|",i,"|",Size(G),"|");;
  first:=true;;
  for gen in GeneratorsOfGroup(G) do
    if not first then Print(";"); fi;;
    first:=false;;
    Print(JoinStringsWithSeparator(List([1..8],j->String(j^gen)),","));;
  od;;
  Print("\n");;
od;;
QUIT;
'''
    process = subprocess.run(
        ["docker", "run", "--rm", "-i", "gapsystem/gap-docker", "gap", "-q"],
        input=gap_code,
        text=True,
        capture_output=True,
        check=True,
    )
    lines = [line.strip() for line in process.stdout.splitlines() if line.strip()]
    assert lines[0] == "COUNT|50"
    groups = []
    for line in lines[1:]:
        tag, index, order, encoded = line.split("|")
        assert tag == "G"
        generators = [
            tuple(int(value) - 1 for value in generator.split(","))
            for generator in encoded.split(";")
        ]
        groups.append((int(index), int(order), generators))
    assert len(groups) == 50
    return groups


def triple_orbits(generators: list[tuple[int, ...]]) -> list[tuple[tuple[int, int, int], ...]]:
    unseen = set(TRIPLES)
    orbits = []
    while unseen:
        seed = min(unseen)
        orbit = {seed}
        frontier = [seed]
        while frontier:
            triple = frontier.pop()
            for generator in generators:
                image = tuple(sorted(generator[vertex] for vertex in triple))
                if image not in orbit:
                    orbit.add(image)
                    frontier.append(image)
        unseen -= orbit
        orbits.append(tuple(sorted(orbit)))
    return orbits


def directed_pair_orbits(
    generators: list[tuple[int, ...]],
) -> list[set[tuple[int, int]]]:
    unseen = {(left, right) for left in range(8) for right in range(8) if left != right}
    orbits = []
    while unseen:
        seed = min(unseen)
        orbit = {seed}
        frontier = [seed]
        while frontier:
            left, right = frontier.pop()
            for generator in generators:
                image = (generator[left], generator[right])
                if image not in orbit:
                    orbit.add(image)
                    frontier.append(image)
        unseen -= orbit
        orbits.append(orbit)
    return orbits


def patterns(
    triple_orbit_list: list[tuple[tuple[int, int, int], ...]],
    generators: list[tuple[int, ...]],
) -> tuple[int, list[tuple[int, ...]]]:
    orbits = triple_orbit_list
    weights = [z3.Int(f"w_{index}") for index in range(len(orbits))]
    solver = z3.Solver()
    solver.add(*(weight >= 0 for weight in weights))
    solver.add(sum(len(orbit) * weight for orbit, weight in zip(orbits, weights)) == 80)
    for vertex in range(8):
        solver.add(
            sum(
                sum(vertex in triple for triple in orbit) * weight
                for orbit, weight in zip(orbits, weights)
            )
            == 30
        )
    for pair in PAIRS:
        solver.add(
            sum(
                sum(set(pair) <= set(triple) for triple in orbit) * weight
                for orbit, weight in zip(orbits, weights)
            )
            <= 10
        )
    pair_orbit_list = directed_pair_orbits(generators)
    total = 0
    omission_orbit_patterns = []
    while solver.check() == z3.sat:
        model = solver.model()
        pattern = tuple(model.eval(weight).as_long() for weight in weights)
        total += 1
        pair_codegree = {
            pair: sum(
                sum(set(pair) <= set(triple) for triple in orbit) * weight
                for orbit, weight in zip(orbits, pattern)
            )
            for pair in PAIRS
        }
        deficits = {
            (left, right): 10 - pair_codegree[tuple(sorted((left, right)))]
            for left in range(8)
            for right in range(8)
            if left != right
        }
        support = {pair for pair, deficit in deficits.items() if deficit != 0}
        if any(support == orbit for orbit in pair_orbit_list):
            values = {deficits[pair] for pair in support}
            if len(values) == 1:
                omission_orbit_patterns.append(pattern)
        solver.add(z3.Or(*(weight != value for weight, value in zip(weights, pattern))))
    return total, omission_orbit_patterns


def main() -> None:
    survivors = 0
    for index, order, generators in gap_transitive_generators():
        orbits = triple_orbits(generators)
        total_patterns, omission_patterns = patterns(orbits, generators)
        if omission_patterns:
            survivors += 1
        pattern_digest = hashlib.sha256(repr(sorted(omission_patterns)).encode()).hexdigest()
        print(
            f"transitive_group={index}",
            f"order={order}",
            f"triple_orbit_sizes={tuple(map(len, orbits))}",
            f"integer_patterns={total_patterns}",
            f"omission_orbit_pattern_count={len(omission_patterns)}",
            f"omission_orbit_pattern_sha256={pattern_digest}",
        )
    print(f"quotient_survivors={survivors}/50")


if __name__ == "__main__":
    main()
