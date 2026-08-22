#!/usr/bin/env python3
"""Lift a surviving Petersen^8 quotient via 24 anti-permutations.

Every surviving quotient is K_{2,2,2,2}: four omitted component pairs and a
perfect Petersen anti-matching on each of the other 24 component pairs.  The
solver chooses those permutations, requires every matched edge to extend to
exactly one triangular block, pins the selected quotient multiplicities, and
adds C4 constraints lazily from concrete models.
"""

from __future__ import annotations

import argparse
from itertools import combinations

import networkx as nx
import z3

from q9_petersen8_quotient_patterns import (
    gap_transitive_generators,
    patterns,
    triple_orbits,
)


def selected_pattern(group_index: int, pattern_index: int):
    _, _, generators = gap_transitive_generators()[group_index - 1]
    orbits = triple_orbits(generators)
    _, surviving = patterns(orbits, generators)
    weights = sorted(surviving)[pattern_index]
    multiplicity = {
        triple: weight
        for orbit, weight in zip(orbits, weights)
        for triple in orbit
    }
    pair_codegree = {
        pair: sum(
            count for triple, count in multiplicity.items()
            if set(pair) <= set(triple)
        )
        for pair in combinations(range(8), 2)
    }
    mate = {
        left: next(
            right for right in range(8)
            if left != right and pair_codegree[tuple(sorted((left, right)))] == 0
        )
        for left in range(8)
    }
    return multiplicity, mate


def target_automorphism_representatives(petersen: nx.Graph) -> list[tuple[int, ...]]:
    compatibility = nx.Graph()
    compatibility.add_nodes_from((left, right) for left in range(10) for right in range(10))
    for left, image_left in compatibility:
        for right, image_right in compatibility:
            if (
                left < right and image_left != image_right
                and not (
                    petersen.has_edge(left, right)
                    and petersen.has_edge(image_left, image_right)
                )
            ):
                compatibility.add_edge((left, image_left), (right, image_right))
    anti_matchings = set()
    for clique in nx.find_cliques(compatibility):
        if len(clique) == 10:
            matching = [0] * 10
            for left, right in clique:
                matching[left] = right
            anti_matchings.add(tuple(matching))
    assert len(anti_matchings) == 2880
    automorphisms = [
        tuple(mapping[vertex] for vertex in range(10))
        for mapping in nx.algorithms.isomorphism.GraphMatcher(
            petersen, petersen
        ).isomorphisms_iter()
    ]
    unseen = set(anti_matchings)
    representatives = []
    while unseen:
        representative = min(unseen)
        orbit = {
            tuple(automorphism[representative[vertex]] for vertex in range(10))
            for automorphism in automorphisms
        }
        assert len(orbit) == 120
        unseen -= orbit
        representatives.append(representative)
    assert len(representatives) == 24
    return representatives


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--group", type=int, required=True)
    parser.add_argument("--pattern", type=int, default=0)
    parser.add_argument("--max-cuts", type=int, default=100000)
    parser.add_argument("--timeout-ms", type=int, default=60000)
    args = parser.parse_args()

    multiplicity, mate = selected_pattern(args.group, args.pattern)
    petersen = nx.petersen_graph()
    anti_representatives = target_automorphism_representatives(petersen)
    solver = z3.SolverFor("QF_BV")
    solver.set(timeout=args.timeout_ms)
    values: dict[tuple[int, int], list[z3.BitVecRef]] = {}

    def lookup(entries, index):
        result = entries[-1]
        for position in reversed(range(9)):
            result = z3.If(index == position, entries[position], result)
        return result

    for left in range(8):
        for right in range(8):
            if left == right or mate[left] == right:
                continue
            entries = [z3.BitVec(f"p_{left}_{right}_{vertex}", 4) for vertex in range(10)]
            values[left, right] = entries
            for entry in entries:
                solver.add(z3.ULT(entry, 10))
            solver.add(z3.Distinct(*entries))

    for left, right in combinations(range(8), 2):
        if mate[left] == right:
            continue
        for vertex in range(10):
            solver.add(
                lookup(values[right, left], values[left, right][vertex]) == vertex
            )
        for source_left, source_right in petersen.edges():
            solver.add(
                z3.Or(
                    *(
                        z3.And(
                            values[left, right][source_left] == image_left,
                            values[left, right][source_right] == image_right,
                        )
                        for image_left in range(10)
                        for image_right in range(10)
                        if image_left != image_right
                        and not petersen.has_edge(image_left, image_right)
                    )
                )
            )

    # Gauge-fix one perfect anti-matching.  The 2,880 choices form one orbit
    # under the two Petersen automorphism groups (verified by the quotient
    # script), so this loses no isomorphism class.
    gauge_pair = next(
        pair for pair in combinations(range(8), 2) if mate[pair[0]] != pair[1]
    )
    gauge_map = (3, 6, 4, 7, 0, 1, 2, 5, 8, 9)
    for vertex, image in enumerate(gauge_map):
        solver.add(values[gauge_pair][vertex] == image)

    component_graph = nx.Graph()
    component_graph.add_nodes_from(range(8))
    component_graph.add_edges_from(
        pair for pair in combinations(range(8), 2) if mate[pair[0]] != pair[1]
    )
    tree = nx.bfs_tree(component_graph, gauge_pair[0])
    assert len(tree.edges()) == 7
    for parent, child in tree.edges():
        if {parent, child} == set(gauge_pair):
            continue
        solver.add(
            z3.Or(
                *(
                    z3.And(
                        *(values[parent, child][vertex] == representative[vertex]
                          for vertex in range(10))
                    )
                    for representative in anti_representatives
                )
            )
        )

    def triangle_condition(i: int, j: int, k: int, vertex: int):
        return values[i, k][vertex] == lookup(
            values[j, k], values[i, j][vertex]
        )

    for left, right in combinations(range(8), 2):
        if mate[left] == right:
            continue
        possible_thirds = [
            third for third in range(8)
            if third not in {left, right}
            and mate[left] != third and mate[right] != third
        ]
        assert len(possible_thirds) == 4
        for vertex in range(10):
            solver.add(
                z3.PbEq(
                    [(triangle_condition(left, right, third, vertex), 1)
                     for third in possible_thirds],
                    1,
                )
            )

    for triple, count in multiplicity.items():
        i, j, k = triple
        if any(mate[left] == right for left, right in combinations(triple, 2)):
            assert count == 0
            continue
        solver.add(
            z3.PbEq(
                [(triangle_condition(i, j, k, vertex), 1) for vertex in range(10)],
                count,
            )
        )

    fixed_edges = {
        tuple(sorted((component * 10 + left, component * 10 + right)))
        for component in range(8)
        for left, right in petersen.edges()
    }

    def edge_condition(left: int, right: int):
        left_component, left_local = divmod(left, 10)
        right_component, right_local = divmod(right, 10)
        if left_component == right_component:
            return tuple(sorted((left, right))) in fixed_edges
        if mate[left_component] == right_component:
            return False
        return values[left_component, right_component][left_local] == right_local

    cut_count = 0
    rounds = 0
    while cut_count <= args.max_cuts:
        result = solver.check()
        if result != z3.sat:
            print(
                f"group={args.group} pattern={args.pattern}",
                f"result={result} rounds={rounds} cuts={cut_count}",
            )
            return
        model = solver.model()
        graph = nx.Graph()
        graph.add_nodes_from(range(80))
        graph.add_edges_from(fixed_edges)
        for left_component, right_component in combinations(range(8), 2):
            if mate[left_component] == right_component:
                continue
            for left_local in range(10):
                right_local = model.eval(
                    values[left_component, right_component][left_local]
                ).as_long()
                graph.add_edge(
                    left_component * 10 + left_local,
                    right_component * 10 + right_local,
                )

        violations = []
        for left, right in combinations(range(80), 2):
            common = sorted(set(graph[left]) & set(graph[right]))
            violations.extend(
                (left, right, first, second)
                for first, second in combinations(common, 2)
            )
        if not violations:
            print(
                f"group={args.group} pattern={args.pattern}",
                f"result=c4_free rounds={rounds} cuts={cut_count}",
            )
            return
        for left, right, first, second in violations:
            conditions = [
                edge_condition(left, first), edge_condition(first, right),
                edge_condition(right, second), edge_condition(second, left),
            ]
            symbolic = [condition for condition in conditions if condition is not True]
            assert symbolic and all(condition is not False for condition in conditions)
            solver.add(z3.Not(z3.And(*symbolic)))
        cut_count += len(violations)
        rounds += 1

    print(
        f"group={args.group} pattern={args.pattern}",
        f"result=cut_limit rounds={rounds} cuts={cut_count}",
    )


if __name__ == "__main__":
    main()
