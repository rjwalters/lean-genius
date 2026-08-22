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
from collections import Counter
from itertools import combinations

import networkx as nx
import z3


TRIPLES = tuple(combinations(range(8), 3))
PAIRS = tuple(combinations(range(8), 2))


def weak_compositions(total: int, parts: int):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in weak_compositions(total - first, parts - 1):
            yield (first,) + rest


TEN_VERTEX_LOCAL_SIGNATURES: set[tuple[int, ...]] | None = None


def ten_vertex_local_signatures() -> set[tuple[int, ...]]:
    """Edge multiplicities obtained from ten 1-factors of K_{2,2,2}."""
    global TEN_VERTEX_LOCAL_SIGNATURES
    if TEN_VERTEX_LOCAL_SIGNATURES is not None:
        return TEN_VERTEX_LOCAL_SIGNATURES
    nodes = range(6)
    mates = {0: 1, 1: 0, 2: 3, 3: 2, 4: 5, 5: 4}
    edges = tuple(
        pair for pair in combinations(nodes, 2) if mates[pair[0]] != pair[1]
    )

    def matchings(remaining: tuple[int, ...]):
        if not remaining:
            yield ()
            return
        first = remaining[0]
        for second in remaining[1:]:
            if mates[first] == second:
                continue
            rest = tuple(vertex for vertex in remaining if vertex not in {first, second})
            for matching in matchings(rest):
                yield (tuple(sorted((first, second))),) + matching

    local_matchings = tuple(sorted(set(matchings(tuple(nodes)))))
    assert len(local_matchings) == 8
    incidence = [tuple(int(edge in matching) for edge in edges) for matching in local_matchings]
    signatures = set()
    for counts in weak_compositions(10, len(local_matchings)):
        signatures.add(
            tuple(
                sum(count * vector[index] for count, vector in zip(counts, incidence))
                for index in range(len(edges))
            )
        )
    TEN_VERTEX_LOCAL_SIGNATURES = signatures
    return signatures


def perfect_matching_agreement_catalog() -> Counter[int]:
    """Exhaust perfect Petersen anti-matchings and their triple agreements."""
    petersen = nx.petersen_graph()
    compatibility = nx.Graph()
    compatibility.add_nodes_from((left, right) for left in range(10) for right in range(10))
    for left, image_left in compatibility:
        for right, image_right in compatibility:
            if (
                left < right
                and image_left != image_right
                and not (
                    petersen.has_edge(left, right)
                    and petersen.has_edge(image_left, image_right)
                )
            ):
                compatibility.add_edge((left, image_left), (right, image_right))
    anti_matchings = []
    for clique in nx.find_cliques(compatibility):
        if len(clique) == 10:
            matching = [0] * 10
            for left, right in clique:
                matching[left] = right
            anti_matchings.append(tuple(matching))
    anti_matchings = sorted(set(anti_matchings))
    assert len(anti_matchings) == 2880

    automorphisms = [
        tuple(mapping[vertex] for vertex in range(10))
        for mapping in nx.algorithms.isomorphism.GraphMatcher(
            petersen, petersen
        ).isomorphisms_iter()
    ]
    assert len(automorphisms) == 120
    representative = anti_matchings[0]
    double_orbit = set()
    for domain_automorphism in automorphisms:
        for range_automorphism in automorphisms:
            image = [0] * 10
            for vertex in range(10):
                image[domain_automorphism[vertex]] = range_automorphism[
                    representative[vertex]
                ]
            double_orbit.add(tuple(image))
    assert double_orbit == set(anti_matchings)

    counts: Counter[int] = Counter()
    for second in anti_matchings:
        composition = tuple(second[representative[vertex]] for vertex in range(10))
        for third in anti_matchings:
            counts[sum(composition[vertex] == third[vertex] for vertex in range(10))] += 1
    return counts


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
            # A perfect matching between two Petersen blocks must send every
            # Petersen edge to a nonedge.  The 2,880 such anti-matchings form
            # one Aut(P) x Aut(P) orbit.  Exhausting triples of anti-matchings
            # gives attainable three-block agreement counts exactly 0..6.
            # Hence a component triple whose three pair codegrees are all ten
            # can carry at most six triangles.
            perfect_triples_valid = all(
                not all(
                    pair_codegree[tuple(sorted(pair))] == 10
                    for pair in combinations(triple, 2)
                )
                or sum(
                    weight for orbit, weight in zip(orbits, pattern)
                    if triple in orbit
                ) <= 6
                for triple in TRIPLES
            )
            local_factorizations_valid = False
            if len(values) == 1 and values == {10}:
                mate = {
                    left: next(
                        right for right in range(8)
                        if left != right and deficits[left, right] == 10
                    )
                    for left in range(8)
                }
                local_factorizations_valid = True
                signatures = ten_vertex_local_signatures()
                for component in range(8):
                    remaining = {
                        vertex for vertex in range(8)
                        if vertex not in {component, mate[component]}
                    }
                    neighbor_pairs = sorted(
                        tuple(sorted((vertex, mate[vertex])))
                        for vertex in remaining if vertex < mate[vertex]
                    )
                    neighbors = [vertex for pair in neighbor_pairs for vertex in pair]
                    assert len(neighbors) == 6
                    neighbor_mates = {
                        neighbors.index(vertex): neighbors.index(mate[vertex])
                        for vertex in neighbors
                    }
                    local_edges = tuple(
                        pair for pair in combinations(range(6), 2)
                        if neighbor_mates[pair[0]] != pair[1]
                    )
                    signature = tuple(
                        next(
                            weight for orbit, weight in zip(orbits, pattern)
                            if tuple(sorted((component, neighbors[left], neighbors[right]))) in orbit
                        )
                        for left, right in local_edges
                    )
                    if signature not in signatures:
                        local_factorizations_valid = False
                        break
            if len(values) == 1 and perfect_triples_valid and local_factorizations_valid:
                omission_orbit_patterns.append(pattern)
        solver.add(z3.Or(*(weight != value for weight, value in zip(weights, pattern))))
    return total, omission_orbit_patterns


def omission_outdegree(
    orbits: list[tuple[tuple[int, int, int], ...]], pattern: tuple[int, ...]
) -> int:
    pair_codegree = {
        pair: sum(
            sum(set(pair) <= set(triple) for triple in orbit) * weight
            for orbit, weight in zip(orbits, pattern)
        )
        for pair in PAIRS
    }
    return sum(pair_codegree[tuple(sorted((0, other)))] != 10 for other in range(1, 8))


def main() -> None:
    agreement_catalog = perfect_matching_agreement_catalog()
    assert agreement_catalog == Counter(
        {0: 2855400, 1: 3241200, 2: 1639800, 3: 472800,
         4: 72600, 5: 10800, 6: 1800}
    )
    print(f"perfect_anti_matching_agreements={dict(sorted(agreement_catalog.items()))}")
    survivors = 0
    for index, order, generators in gap_transitive_generators():
        orbits = triple_orbits(generators)
        total_patterns, omission_patterns = patterns(orbits, generators)
        if omission_patterns:
            survivors += 1
        pattern_digest = hashlib.sha256(repr(sorted(omission_patterns)).encode()).hexdigest()
        omission_outdegrees = Counter(
            omission_outdegree(orbits, pattern) for pattern in omission_patterns
        )
        print(
            f"transitive_group={index}",
            f"order={order}",
            f"triple_orbit_sizes={tuple(map(len, orbits))}",
            f"integer_patterns={total_patterns}",
            f"omission_orbit_pattern_count={len(omission_patterns)}",
            f"omission_outdegrees={dict(sorted(omission_outdegrees.items()))}",
            f"omission_orbit_pattern_sha256={pattern_digest}",
        )
    print(f"quotient_survivors={survivors}/50")


if __name__ == "__main__":
    main()
