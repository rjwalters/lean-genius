#!/usr/bin/env python3
"""Direct-CNF Petersen^8 lift verifier using Kissat.

This is the certificate-oriented encoding of the perfect-matching lift.
Unlike the exploratory Z3 model, every finite-domain choice is expanded to
Boolean permutation entries and the resulting CNF is sent to Kissat.
Concrete C4 violations are added in batches until SAT with no C4, UNSAT, or
the configured round limit.
"""

from __future__ import annotations

import argparse
import subprocess
import tempfile
from itertools import combinations
from pathlib import Path

import networkx as nx

from q9_petersen8_perfect_matching_lift import (
    selected_pattern,
    target_automorphism_representatives,
)
from q9_petersen8_quotient_patterns import gap_transitive_generators


class Cnf:
    def __init__(self) -> None:
        self.names: dict[tuple, int] = {}
        self.clauses: list[list[int]] = []

    def var(self, name: tuple) -> int:
        if name not in self.names:
            self.names[name] = len(self.names) + 1
        return self.names[name]

    def add(self, *literals: int) -> None:
        self.clauses.append(list(literals))

    def exactly_one(self, variables: list[int]) -> None:
        self.add(*variables)
        for left, right in combinations(variables, 2):
            self.add(-left, -right)

    def exact_cardinality(self, variables: list[int], count: int) -> None:
        for subset in combinations(variables, count + 1):
            self.add(*(-variable for variable in subset))
        for subset in combinations(variables, len(variables) - count + 1):
            self.add(*subset)

    def write(self, path: Path) -> None:
        with path.open("w") as output:
            output.write(f"p cnf {len(self.names)} {len(self.clauses)}\n")
            for clause in self.clauses:
                output.write(" ".join(map(str, clause)) + " 0\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--group", type=int, required=True)
    parser.add_argument("--pattern", type=int, default=0)
    parser.add_argument("--max-rounds", type=int, default=100)
    parser.add_argument("--time-seconds", type=int, default=60)
    parser.add_argument("--without-action", action="store_true")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    multiplicity, mate = selected_pattern(args.group, args.pattern)
    petersen = nx.petersen_graph()
    cnf = Cnf()

    supported_pairs = [
        pair for pair in combinations(range(8), 2) if mate[pair[0]] != pair[1]
    ]

    def x(left: int, right: int, source: int, target: int) -> int:
        if left < right:
            return cnf.var(("x", left, right, source, target))
        return cnf.var(("x", right, left, target, source))

    for left, right in supported_pairs:
        for source in range(10):
            cnf.exactly_one([x(left, right, source, target) for target in range(10)])
        for target in range(10):
            cnf.exactly_one([x(left, right, source, target) for source in range(10)])
        for source_left, source_right in petersen.edges():
            for target_left, target_right in petersen.edges():
                cnf.add(
                    -x(left, right, source_left, target_left),
                    -x(left, right, source_right, target_right),
                )
                cnf.add(
                    -x(left, right, source_left, target_right),
                    -x(left, right, source_right, target_left),
                )

    def triangle(i: int, j: int, k: int, vertex: int) -> int:
        assert i < j < k
        return cnf.var(("triangle", i, j, k, vertex))

    supported_triples = [
        triple for triple in combinations(range(8), 3)
        if all(mate[left] != right for left, right in combinations(triple, 2))
    ]
    for i, j, k in supported_triples:
        for source in range(10):
            agreement = triangle(i, j, k, source)
            for middle in range(10):
                for target in range(10):
                    # Once the i->j and i->k images are selected, agreement
                    # is exactly the corresponding j->k matching entry.
                    cnf.add(
                        -x(i, j, source, middle),
                        -x(i, k, source, target),
                        -agreement,
                        x(j, k, middle, target),
                    )
                    cnf.add(
                        -x(i, j, source, middle),
                        -x(i, k, source, target),
                        agreement,
                        -x(j, k, middle, target),
                    )
        cnf.exact_cardinality(
            [triangle(i, j, k, source) for source in range(10)],
            multiplicity[i, j, k],
        )

    for left, right in supported_pairs:
        thirds = [
            third for third in range(8)
            if third not in {left, right}
            and mate[left] != third and mate[right] != third
        ]
        assert len(thirds) == 4
        for source in range(10):
            local_triangles = []
            for third in thirds:
                triple = tuple(sorted((left, right, third)))
                # Express the triangle using its vertex in the least-indexed
                # block.  If `left` is not least, transport `source` through
                # the appropriate matching with implication clauses.
                if left == triple[0]:
                    local_triangles.append(triangle(*triple, source))
                else:
                    auxiliary = cnf.var(("edge_triangle", left, right, third, source))
                    least = triple[0]
                    for least_vertex in range(10):
                        map_literal = x(least, left, least_vertex, source)
                        tri_literal = triangle(*triple, least_vertex)
                        cnf.add(-map_literal, -auxiliary, tri_literal)
                        cnf.add(-map_literal, auxiliary, -tri_literal)
                    local_triangles.append(auxiliary)
            cnf.exactly_one(local_triangles)

    # Lossless spanning-tree gauge under independent target-block
    # automorphisms.  Fix the first edge completely and restrict each later
    # tree edge to 24 target-automorphism representatives.
    representatives = target_automorphism_representatives(petersen)
    component_graph = nx.Graph()
    component_graph.add_nodes_from(range(8))
    component_graph.add_edges_from(supported_pairs)
    tree_edges = list(nx.bfs_edges(component_graph, 0))
    assert len(tree_edges) == 7
    gauge_map = (3, 6, 4, 7, 0, 1, 2, 5, 8, 9)
    root_left, root_right = tree_edges[0]
    for source, target in enumerate(gauge_map):
        cnf.add(x(root_left, root_right, source, target))
    for edge_index, (parent, child) in enumerate(tree_edges[1:], start=1):
        selectors = [cnf.var(("gauge", edge_index, index)) for index in range(24)]
        cnf.exactly_one(selectors)
        for selector, representative in zip(selectors, representatives):
            for source, target in enumerate(representative):
                cnf.add(-selector, x(parent, child, source, target))

    if not args.without_action:
        _, _, component_generators = gap_transitive_generators()[args.group - 1]

        def y(generator_index: int, component: int, source: int, target: int) -> int:
            return cnf.var(("action", generator_index, component, source, target))

        petersen_edges = {tuple(sorted(edge)) for edge in petersen.edges()}
        petersen_nonedges = [
            pair for pair in combinations(range(10), 2) if pair not in petersen_edges
        ]
        for generator_index, generator in enumerate(component_generators):
            for component in range(8):
                for source in range(10):
                    cnf.exactly_one(
                        [y(generator_index, component, source, target)
                         for target in range(10)]
                    )
                for target in range(10):
                    cnf.exactly_one(
                        [y(generator_index, component, source, target)
                         for source in range(10)]
                    )
                for source_left, source_right in petersen.edges():
                    for target_left, target_right in petersen_nonedges:
                        cnf.add(
                            -y(generator_index, component, source_left, target_left),
                            -y(generator_index, component, source_right, target_right),
                        )
                        cnf.add(
                            -y(generator_index, component, source_left, target_right),
                            -y(generator_index, component, source_right, target_left),
                        )

            # Each lifted generator conjugates every cross-block matching to
            # the matching on the image component pair.
            for left, right in supported_pairs:
                image_left, image_right = generator[left], generator[right]
                for source in range(10):
                    for target in range(10):
                        source_edge = x(left, right, source, target)
                        for image_source in range(10):
                            left_action = y(
                                generator_index, left, source, image_source
                            )
                            for image_target in range(10):
                                right_action = y(
                                    generator_index, right, target, image_target
                                )
                                image_edge = x(
                                    image_left, image_right, image_source, image_target
                                )
                                cnf.add(
                                    -source_edge, -left_action, -right_action, image_edge
                                )

    fixed_edges = {
        tuple(sorted((component * 10 + left, component * 10 + right)))
        for component in range(8)
        for left, right in petersen.edges()
    }

    def edge_literal(left: int, right: int) -> int | bool:
        left_component, left_local = divmod(left, 10)
        right_component, right_local = divmod(right, 10)
        if left_component == right_component:
            return tuple(sorted((left, right))) in fixed_edges
        if mate[left_component] == right_component:
            return False
        return x(left_component, right_component, left_local, right_local)

    for round_index in range(args.max_rounds + 1):
        with tempfile.TemporaryDirectory(prefix="q9-petersen8-") as directory:
            cnf_path = Path(directory) / "lift.cnf"
            cnf.write(cnf_path)
            process = subprocess.run(
                ["kissat", "--quiet", "--unsat", f"--seed={args.seed}",
                 f"--time={args.time_seconds}", str(cnf_path)],
                text=True,
                capture_output=True,
            )
        if process.returncode == 20:
            print(
                f"group={args.group} pattern={args.pattern} result=unsat",
                f"rounds={round_index} variables={len(cnf.names)} clauses={len(cnf.clauses)}",
            )
            return
        if process.returncode == 0:
            print(
                f"group={args.group} pattern={args.pattern} result=unknown",
                f"rounds={round_index} variables={len(cnf.names)} clauses={len(cnf.clauses)}",
            )
            return
        if process.returncode != 10:
            raise RuntimeError(process.stdout + process.stderr)
        positive = {
            int(literal)
            for line in process.stdout.splitlines() if line.startswith("v ")
            for literal in line.split()[1:] if int(literal) > 0
        }
        graph = nx.Graph()
        graph.add_nodes_from(range(80))
        graph.add_edges_from(fixed_edges)
        for left, right in supported_pairs:
            for source in range(10):
                target = next(
                    target for target in range(10)
                    if x(left, right, source, target) in positive
                )
                graph.add_edge(left * 10 + source, right * 10 + target)

        violations = []
        for left, right in combinations(range(80), 2):
            common = sorted(set(graph[left]) & set(graph[right]))
            violations.extend(
                (left, right, first, second)
                for first, second in combinations(common, 2)
            )
        if not violations:
            print(
                f"group={args.group} pattern={args.pattern} result=c4_free",
                f"rounds={round_index} variables={len(cnf.names)} clauses={len(cnf.clauses)}",
            )
            return
        for left, right, first, second in violations:
            conditions = [
                edge_literal(left, first), edge_literal(first, right),
                edge_literal(right, second), edge_literal(second, left),
            ]
            symbolic = [condition for condition in conditions if condition is not True]
            assert symbolic and all(condition is not False for condition in conditions)
            cnf.add(*(-literal for literal in symbolic))

    print(
        f"group={args.group} pattern={args.pattern} result=round_limit",
        f"rounds={args.max_rounds} variables={len(cnf.names)} clauses={len(cnf.clauses)}",
    )


if __name__ == "__main__":
    main()
