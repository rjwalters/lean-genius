#!/usr/bin/env python3
"""Classify the five-block quotients for the q=9 order-16x5 shadow.

The internal-edge sieve proves that every configuration line meets three
distinct shadow components.  Thus the 80 lines give a weighted 3-uniform
hypergraph on five blocks, invariant under a transitive degree-five group,
with weighted degree 48 at every block.  This script exhausts the five
transitive groups and all nonnegative invariant integer weightings.

Equivalently, complementing a block triple gives a weighted graph on five
vertices with total weight 80 and weighted degree 32 at every vertex.
"""

from __future__ import annotations

import hashlib
import subprocess
from itertools import combinations

import z3


TRIPLES = tuple(combinations(range(5), 3))
PAIRS = tuple(combinations(range(5), 2))


def gap_transitive_generators() -> list[tuple[int, int, list[tuple[int, ...]]]]:
    gap_code = r'''
SizeScreen([100000,100000]);;
Print("COUNT|",NrTransitiveGroups(5),"\n");;
for i in [1..NrTransitiveGroups(5)] do
  G:=TransitiveGroup(5,i);;
  Print("G|",i,"|",Size(G),"|");;
  first:=true;;
  for gen in GeneratorsOfGroup(G) do
    if not first then Print(";"); fi;;
    first:=false;;
    Print(JoinStringsWithSeparator(List([1..5],j->String(j^gen)),","));;
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
    assert lines[0] == "COUNT|5"
    groups = []
    for line in lines[1:]:
        tag, index, order, encoded = line.split("|")
        assert tag == "G"
        generators = [
            tuple(int(value) - 1 for value in generator.split(","))
            for generator in encoded.split(";")
        ]
        groups.append((int(index), int(order), generators))
    assert len(groups) == 5
    return groups


def set_orbits(
    objects: tuple[tuple[int, ...], ...], generators: list[tuple[int, ...]]
) -> list[tuple[tuple[int, ...], ...]]:
    unseen = set(objects)
    orbits = []
    while unseen:
        seed = min(unseen)
        orbit = {seed}
        frontier = [seed]
        while frontier:
            item = frontier.pop()
            for generator in generators:
                image = tuple(sorted(generator[vertex] for vertex in item))
                if image not in orbit:
                    orbit.add(image)
                    frontier.append(image)
        unseen -= orbit
        orbits.append(tuple(sorted(orbit)))
    return orbits


def invariant_patterns(
    triple_orbits: list[tuple[tuple[int, ...], ...]],
) -> list[tuple[int, ...]]:
    weights = [z3.Int(f"w_{index}") for index in range(len(triple_orbits))]
    solver = z3.Solver()
    solver.add(*(weight >= 0 for weight in weights))
    solver.add(
        sum(len(orbit) * weight for orbit, weight in zip(triple_orbits, weights))
        == 80
    )
    for block in range(5):
        solver.add(
            sum(
                sum(block in triple for triple in orbit) * weight
                for orbit, weight in zip(triple_orbits, weights)
            )
            == 48
        )
    patterns = []
    while solver.check() == z3.sat:
        model = solver.model()
        pattern = tuple(model.eval(weight).as_long() for weight in weights)
        patterns.append(pattern)
        solver.add(z3.Or(*(weight != value for weight, value in zip(weights, pattern))))
    return sorted(patterns)


def pair_codegrees(
    triple_orbits: list[tuple[tuple[int, ...], ...]], pattern: tuple[int, ...]
) -> tuple[int, ...]:
    return tuple(
        sum(
            sum(set(pair) <= set(triple) for triple in orbit) * weight
            for orbit, weight in zip(triple_orbits, pattern)
        )
        for pair in PAIRS
    )


def main() -> None:
    total = 0
    for index, order, generators in gap_transitive_generators():
        triple_orbits = set_orbits(TRIPLES, generators)
        patterns = invariant_patterns(triple_orbits)
        total += len(patterns)
        assert all(
            sum(len(orbit) * weight for orbit, weight in zip(triple_orbits, pattern))
            == 80
            for pattern in patterns
        )
        codegree_catalog = sorted({pair_codegrees(triple_orbits, p) for p in patterns})
        digest = hashlib.sha256(repr(patterns).encode()).hexdigest()
        print(
            f"transitive_group={index}",
            f"order={order}",
            f"triple_orbit_sizes={tuple(map(len, triple_orbits))}",
            f"pattern_count={len(patterns)}",
            f"pattern_sha256={digest}",
        )
        print(f"  patterns={patterns}")
        print(f"  pair_codegrees={codegree_catalog}")
    assert total == 37
    print("quotient_actions=5 quotient_patterns=37")


if __name__ == "__main__":
    main()
