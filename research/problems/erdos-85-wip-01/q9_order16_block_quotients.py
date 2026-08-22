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


def compose(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(left[right[vertex]] for vertex in range(5))


def generated_group(generators: list[tuple[int, ...]]) -> set[tuple[int, ...]]:
    identity = tuple(range(5))
    group = {identity}
    frontier = list(generators)
    while frontier:
        permutation = frontier.pop()
        if permutation in group:
            continue
        previous = list(group)
        group.add(permutation)
        for other in previous:
            frontier.append(compose(permutation, other))
            frontier.append(compose(other, permutation))
    return group


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


def point_stabilizer_integral_patterns(
    triple_orbits: list[tuple[tuple[int, ...], ...]],
    patterns: list[tuple[int, ...]],
    generators: list[tuple[int, ...]],
) -> tuple[list[int], list[tuple[int, ...]]]:
    """Apply integrality on the line orbits incident with one component.

    The component stabilizer is transitive on its 16 vertices.  On every
    orbit O of block triples containing block zero, the number of incident
    lines is therefore 16 times the number through one vertex.  Hence the
    sum of the triple weights on O must be divisible by 16.
    """
    group = generated_group(generators)
    stabilizer = [permutation for permutation in group if permutation[0] == 0]
    incident = tuple(triple for triple in TRIPLES if 0 in triple)
    stabilizer_orbits = set_orbits(incident, stabilizer)
    orbit_index = {
        triple: index
        for index, orbit in enumerate(triple_orbits)
        for triple in orbit
    }
    survivors = [
        pattern
        for pattern in patterns
        if all(
            sum(pattern[orbit_index[triple]] for triple in orbit) % 16 == 0
            for orbit in stabilizer_orbits
        )
    ]
    return list(map(len, stabilizer_orbits)), survivors


def main() -> None:
    total = 0
    lift_total = 0
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
        stabilizer_orbit_sizes, lift_patterns = point_stabilizer_integral_patterns(
            triple_orbits, patterns, generators
        )
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
        print(
            f"  point_stabilizer_incident_orbit_sizes={stabilizer_orbit_sizes}",
            f"integral_lift_patterns={lift_patterns}",
        )
        lift_total += len(lift_patterns)
    assert total == 37
    assert lift_total == 7
    print("quotient_actions=5 quotient_patterns=37")
    print("point_stabilizer_integral_lift_patterns=7")


if __name__ == "__main__":
    main()
