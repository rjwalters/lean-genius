#!/usr/bin/env python3
"""Test the endpoint block quotient for the q=9 order-16x5 shadow.

After block-stabilizer integrality, the C5 and D10 quotient cases have one
of the two five-triple orbits at weight 16 and the other at weight zero.
The two supports are isomorphic under a relabelling of the five blocks, so
one support suffices.  This verifier encodes all 80-line lifts of that
support, independent of any further vertex-transitivity assumption.

The base solver enforces the line counts, one line through every point for
each incident block triple, and linearity.  Candidate models are then cut by
every intrinsic-shadow violation and every C4 found in the union of the
cubic shadow and triangular graph.  UNSAT therefore excludes all four
endpoint action-pattern pairs at once.
"""

from __future__ import annotations

import argparse
import hashlib
import subprocess
import sys
from collections import defaultdict
from itertools import combinations, combinations_with_replacement, permutations, product
from pathlib import Path

import networkx as nx
import z3


EXPECTED_SHA256 = "4bac89beec1465265318266117c38a2c1680e73a21efd322411207cef5313088"
ENDPOINT_BLOCK_TRIPLES = (
    (0, 1, 2),
    (0, 1, 4),
    (0, 3, 4),
    (1, 2, 3),
    (2, 3, 4),
)
UNIFORM_BLOCK_TRIPLES = tuple(combinations(range(5), 3))

FIBER_PARTITIONS_4 = (
    ((0, 1, 5, 15), (2, 9, 13, 14), (3, 7, 8, 11), (4, 6, 10, 12)),
    ((0, 2, 5, 13), (1, 4, 10, 15), (3, 6, 11, 12), (7, 8, 9, 14)),
    ((0, 2, 5, 13), (1, 7, 8, 15), (3, 6, 11, 12), (4, 9, 10, 14)),
    ((0, 2, 5, 13), (1, 9, 14, 15), (3, 6, 11, 12), (4, 7, 8, 10)),
    ((0, 3, 5, 11), (1, 4, 10, 15), (2, 6, 12, 13), (7, 8, 9, 14)),
    ((0, 3, 5, 11), (1, 7, 8, 15), (2, 6, 12, 13), (4, 9, 10, 14)),
    ((0, 3, 5, 11), (1, 9, 14, 15), (2, 6, 12, 13), (4, 7, 8, 10)),
    ((0, 4, 5, 10), (1, 2, 13, 15), (3, 9, 11, 14), (6, 7, 8, 12)),
    ((0, 4, 5, 10), (1, 3, 11, 15), (2, 7, 8, 13), (6, 9, 12, 14)),
    ((0, 4, 5, 10), (1, 6, 12, 15), (2, 7, 8, 13), (3, 9, 11, 14)),
    ((0, 5, 6, 12), (1, 4, 10, 15), (2, 3, 11, 13), (7, 8, 9, 14)),
    ((0, 5, 6, 12), (1, 7, 8, 15), (2, 3, 11, 13), (4, 9, 10, 14)),
    ((0, 5, 6, 12), (1, 9, 14, 15), (2, 3, 11, 13), (4, 7, 8, 10)),
    ((0, 5, 7, 8), (1, 2, 13, 15), (3, 4, 10, 11), (6, 9, 12, 14)),
    ((0, 5, 7, 8), (1, 3, 11, 15), (2, 4, 10, 13), (6, 9, 12, 14)),
    ((0, 5, 7, 8), (1, 6, 12, 15), (2, 4, 10, 13), (3, 9, 11, 14)),
    ((0, 5, 9, 14), (1, 2, 13, 15), (3, 4, 10, 11), (6, 7, 8, 12)),
    ((0, 5, 9, 14), (1, 3, 11, 15), (2, 4, 10, 13), (6, 7, 8, 12)),
    ((0, 5, 9, 14), (1, 6, 12, 15), (2, 7, 8, 13), (3, 4, 10, 11)),
)

FIBER_PARTITIONS_8 = (
    ((0, 1, 2, 5, 9, 13, 14, 15), (3, 4, 6, 7, 8, 10, 11, 12)),
    ((0, 1, 3, 5, 7, 8, 11, 15), (2, 4, 6, 9, 10, 12, 13, 14)),
    ((0, 1, 4, 5, 6, 10, 12, 15), (2, 3, 7, 8, 9, 11, 13, 14)),
    ((0, 2, 3, 5, 6, 11, 12, 13), (1, 4, 7, 8, 9, 10, 14, 15)),
    ((0, 2, 4, 5, 7, 8, 10, 13), (1, 3, 6, 9, 11, 12, 14, 15)),
    ((0, 3, 4, 5, 9, 10, 11, 14), (1, 2, 6, 7, 8, 12, 13, 15)),
    ((0, 5, 6, 7, 8, 9, 12, 14), (1, 2, 3, 4, 10, 11, 13, 15)),
)


def component_ordinal_4(raw: bytes) -> nx.Graph:
    ordinal = 0
    for line in raw.splitlines():
        if not line.strip():
            continue
        try:
            graph = nx.from_graph6_bytes(line.strip())
        except nx.NetworkXError:
            graph = nx.from_sparse6_bytes(line.strip())
        if len(graph) != 16:
            continue
        ordinal += 1
        if ordinal == 4:
            return nx.convert_node_labels_to_integers(graph)
    raise AssertionError("missing order-16 ordinal 4")


def shadow_product(component: nx.Graph) -> nx.Graph:
    shadow = nx.Graph()
    shadow.add_nodes_from(range(80))
    for block in range(5):
        shadow.add_edges_from(
            (16 * block + left, 16 * block + right)
            for left, right in component.edges()
        )
    return shadow


def centered_c4s(graph: nx.Graph) -> set[tuple[int, int, int, int]]:
    centers_by_endpoints: dict[tuple[int, int], list[int]] = defaultdict(list)
    for center in graph:
        for endpoints in combinations(sorted(graph[center]), 2):
            centers_by_endpoints[endpoints].append(center)
    cycles = set()
    for (left, right), centers in centers_by_endpoints.items():
        for first, second in combinations(centers, 2):
            cycles.add((left, first, right, second))
    return cycles


def a4_three_line_pattern_orbits() -> list[set[tuple[int, ...]]]:
    """A4 orbits on three-line multisets over the six incident triples."""
    vertices = range(4)
    pairs = list(combinations(vertices, 2))
    even_permutations = [
        permutation
        for permutation in permutations(vertices)
        if sum(
            permutation[left] > permutation[right]
            for left, right in combinations(vertices, 2)
        )
        % 2
        == 0
    ]
    actions = [
        tuple(
            pairs.index(tuple(sorted((permutation[left], permutation[right]))))
            for left, right in pairs
        )
        for permutation in even_permutations
    ]
    unseen = {
        tuple(multiset.count(index) for index in range(6))
        for multiset in combinations_with_replacement(range(6), 3)
    }
    orbits = []
    while unseen:
        pattern = min(unseen)
        orbit = {
            tuple(pattern[action.index(index)] for index in range(6))
            for action in actions
        }
        unseen -= orbit
        orbits.append(orbit)
    assert sorted(map(len, orbits)) == [4, 4, 6, 6, 6, 6, 12, 12]
    liftable = [orbit for orbit in orbits if 16 % len(orbit) == 0]
    assert len(liftable) == 2
    assert all(
        all(set(pattern) <= {0, 1} for pattern in orbit) for orbit in liftable
    )
    return orbits


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("census", type=Path)
    parser.add_argument("--backend", choices=("kissat", "z3"), default="kissat")
    parser.add_argument("--rotation-class", type=int)
    parser.add_argument("--seed-orbit", type=int)
    parser.add_argument("--all", action="store_true")
    parser.add_argument(
        "--quotient", choices=("endpoint", "uniform"), default="endpoint"
    )
    parser.add_argument(
        "--stabilizer",
        choices=("none", "f20", "a5-star", "a5-triangle"),
        default="none",
    )
    parser.add_argument("--encoding", choices=("direct", "lazy"), default="direct")
    parser.add_argument("--max-rounds", type=int, default=200)
    parser.add_argument("--kissat-mode", choices=("sat", "unsat"), default="unsat")
    parser.add_argument("--kissat-seed", type=int, default=0)
    parser.add_argument("--f20-pattern", type=int)
    parser.add_argument("--fiber-partition", type=int)
    parser.add_argument("--fiber-bijection", type=int)
    parser.add_argument("--a5-fiber-partition", type=int)
    parser.add_argument("--a5-fiber-bijection", type=int)
    args = parser.parse_args()
    raw = args.census.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_SHA256
    component = component_ordinal_4(raw)
    shadow = shadow_product(component)
    block_triples = (
        ENDPOINT_BLOCK_TRIPLES
        if args.quotient == "endpoint"
        else UNIFORM_BLOCK_TRIPLES
    )
    block_triple_weight = 16 if args.quotient == "endpoint" else 8
    if args.stabilizer in ("a5-star", "a5-triangle"):
        a4_three_line_pattern_orbits()

    automorphisms = sorted(
        tuple(mapping[vertex] for vertex in range(16))
        for mapping in nx.algorithms.isomorphism.GraphMatcher(
            component, component
        ).isomorphisms_iter()
    )
    assert len(automorphisms) == 96

    def compose(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
        return tuple(left[right[vertex]] for vertex in range(16))

    def inverse(permutation: tuple[int, ...]) -> tuple[int, ...]:
        result = [0] * 16
        for vertex, image in enumerate(permutation):
            result[image] = vertex
        return tuple(result)

    unseen_automorphisms = set(automorphisms)
    rotation_classes = []
    while unseen_automorphisms:
        representative = min(unseen_automorphisms)
        conjugacy_class = {
            compose(compose(group_element, representative), inverse(group_element))
            for group_element in automorphisms
        }
        unseen_automorphisms -= conjugacy_class
        rotation_classes.append((representative, len(conjugacy_class)))
    rotation_classes.sort()
    assert [size for _, size in rotation_classes] == [
        1, 8, 12, 12, 8, 8, 2, 6, 8, 12, 12, 6, 1
    ]
    if args.all:
        assert args.rotation_class is None and args.seed_orbit is None
        completed = 0
        for rotation_class in range(len(rotation_classes)):
            seed_orbits = range(56) if rotation_class == 0 else (None,)
            for seed_orbit in seed_orbits:
                command = [
                    sys.executable,
                    str(Path(__file__).resolve()),
                    str(args.census),
                    "--backend",
                    args.backend,
                    "--rotation-class",
                    str(rotation_class),
                    "--quotient",
                    args.quotient,
                    "--stabilizer",
                    args.stabilizer,
                    "--encoding",
                    args.encoding,
                    "--kissat-mode",
                    args.kissat_mode,
                    "--kissat-seed",
                    str(args.kissat_seed),
                ]
                if seed_orbit is not None:
                    command.extend(("--seed-orbit", str(seed_orbit)))
                if args.f20_pattern is not None:
                    command.extend(("--f20-pattern", str(args.f20_pattern)))
                if args.fiber_partition is not None:
                    command.extend(("--fiber-partition", str(args.fiber_partition)))
                if args.fiber_bijection is not None:
                    command.extend(("--fiber-bijection", str(args.fiber_bijection)))
                process = subprocess.run(command, text=True, capture_output=True)
                if process.returncode != 0 or "UNSAT backend=" not in process.stdout:
                    sys.stdout.write(process.stdout)
                    sys.stderr.write(process.stderr)
                    raise RuntimeError(
                        f"incomplete rotation branch class={rotation_class} "
                        f"seed={seed_orbit} status={process.returncode}"
                    )
                completed += 1
                print(
                    f"completed_rotation_class={rotation_class}",
                    f"seed_orbit={seed_orbit}",
                    flush=True,
                )
        assert completed == 68
        print("UNSAT rotation_branches=68")
        print(f"excluded_quotient={args.quotient}")
        return
    if args.rotation_class is None:
        print(
            "rotation_classes",
            [(index, size) for index, (_, size) in enumerate(rotation_classes)],
        )
        return
    alpha, alpha_class_size = rotation_classes[args.rotation_class]
    print(
        f"rotation_class={args.rotation_class}",
        f"class_size={alpha_class_size}",
        flush=True,
    )

    lines = []
    by_block_triple = defaultdict(list)
    by_point_and_block_triple = defaultdict(list)
    by_pair = defaultdict(list)
    for block_triple in block_triples:
        for local_points in product(range(16), repeat=3):
            line = tuple(
                16 * block + point
                for block, point in zip(block_triple, local_points)
            )
            index = len(lines)
            lines.append(line)
            by_block_triple[block_triple].append(index)
            for point in line:
                by_point_and_block_triple[(point, block_triple)].append(index)
            for pair in combinations(line, 2):
                by_pair[pair].append(index)
    line_to_index = {line: index for index, line in enumerate(lines)}

    chosen = [z3.Bool(f"line_{index}") for index in range(len(lines))]
    triangular_edge = {
        pair: z3.Bool(f"edge_{pair[0]}_{pair[1]}") for pair in by_pair
    }
    solver = z3.Solver()
    centralizer = [
        beta
        for beta in automorphisms
        if compose(beta, alpha) == compose(alpha, beta)
    ]
    unseen_seed_lines = set(product(range(16), repeat=3))
    seed_orbit_representatives = []
    while unseen_seed_lines:
        seed = min(unseen_seed_lines)
        orbit = {
            tuple(beta[point] for point in seed) for beta in centralizer
        }
        unseen_seed_lines -= orbit
        seed_orbit_representatives.append(min(orbit))
    if args.rotation_class == 0:
        assert len(seed_orbit_representatives) == 56
    # The first supported block triple contains 16 selected lines.  Conjugate
    # the normalized rotation by an element of C_A(alpha) so that any one of
    # them is the least representative of its diagonal centralizer orbit.
    # The disjunction covers every orbit and is therefore lossless.
    seed_variables = [
        chosen[
            line_to_index[
                tuple(16 * block + point for block, point in enumerate(seed))
            ]
        ]
        for seed in seed_orbit_representatives
    ]
    if args.seed_orbit is None:
        solver.add(z3.Or(*seed_variables))
        representative_indices = {
            first * 256 + second * 16 + third
            for first, second, third in seed_orbit_representatives
        }
        seed_line_variables = [chosen[index] for index in range(16**3)]
        prefix = seed_line_variables[0]
        for index in range(1, len(seed_line_variables)):
            if index not in representative_indices:
                solver.add(z3.Implies(seed_line_variables[index], prefix))
            prefix = z3.Or(prefix, seed_line_variables[index])
    else:
        solver.add(seed_variables[args.seed_orbit])
    print(
        f"centralizer_order={len(centralizer)}",
        f"seed_orbits={len(seed_orbit_representatives)}",
        f"seed_orbit={args.seed_orbit}",
        flush=True,
    )
    def rotation(point: int) -> int:
        block, local_point = divmod(point, 16)
        if block < 4:
            return point + 16
        return alpha[local_point]

    line_image = []
    for index, line in enumerate(lines):
        image = tuple(sorted(rotation(point) for point in line))
        image_index = line_to_index[image]
        line_image.append(image_index)
        solver.add(chosen[index] == chosen[image_index])
    unseen_line_indices = set(range(len(lines)))
    line_rotation_orbits = []
    while unseen_line_indices:
        seed = min(unseen_line_indices)
        orbit = {seed}
        image_index = line_image[seed]
        while image_index not in orbit:
            orbit.add(image_index)
            image_index = line_image[image_index]
        unseen_line_indices -= orbit
        line_rotation_orbits.append(orbit)
    for block_triple in block_triples:
        solver.add(
            z3.PbEq(
                [(chosen[i], 1) for i in by_block_triple[block_triple]],
                block_triple_weight,
            )
        )
        if args.quotient == "endpoint":
            for block in block_triple:
                for local_point in range(16):
                    point = 16 * block + local_point
                    solver.add(
                        z3.PbEq(
                            [
                                (chosen[i], 1)
                                for i in by_point_and_block_triple[
                                    (point, block_triple)
                                ]
                            ],
                            1,
                        )
                    )
    if args.quotient == "uniform":
        for point in range(80):
            incident_indices = [
                index
                for (indexed_point, _), indices in by_point_and_block_triple.items()
                if indexed_point == point
                for index in indices
            ]
            solver.add(
                z3.PbEq([(chosen[index], 1) for index in incident_indices], 3)
            )
        if args.stabilizer == "f20":
            for block in range(5):
                multiplier = tuple(
                    (block + 2 * (vertex - block)) % 5 for vertex in range(5)
                )
                stabilizer = {tuple(range(5))}
                current = multiplier
                while current not in stabilizer:
                    stabilizer.add(current)
                    current = tuple(multiplier[current[v]] for v in range(5))
                assert len(stabilizer) == 4
                incident_triples = {
                    triple for triple in block_triples if block in triple
                }
                triple_orbits = []
                while incident_triples:
                    seed = min(incident_triples)
                    orbit = {
                        tuple(sorted(permutation[v] for v in seed))
                        for permutation in stabilizer
                    }
                    incident_triples -= orbit
                    triple_orbits.append(orbit)
                assert sorted(map(len, triple_orbits)) == [2, 4]
                for local_point in range(16):
                    point = 16 * block + local_point
                    for orbit in triple_orbits:
                        indices = [
                            index
                            for triple in orbit
                            for index in by_point_and_block_triple[(point, triple)]
                        ]
                        solver.add(
                            z3.PbEq(
                                [(chosen[index], 1) for index in indices],
                                len(orbit) // 2,
                            )
                        )
            if args.f20_pattern is not None:
                base_triples = sorted(
                    triple for triple in block_triples if 0 in triple
                )
                multiplier = tuple(2 * vertex % 5 for vertex in range(5))
                stabilizer = {tuple(range(5))}
                current = multiplier
                while current not in stabilizer:
                    stabilizer.add(current)
                    current = tuple(multiplier[current[v]] for v in range(5))
                triple_actions = [
                    tuple(
                        base_triples.index(
                            tuple(sorted(permutation[v] for v in triple))
                        )
                        for triple in base_triples
                    )
                    for permutation in stabilizer
                ]
                unseen_patterns = {
                    tuple(multiset.count(index) for index in range(6))
                    for multiset in combinations_with_replacement(range(6), 3)
                }
                pattern_orbits = []
                while unseen_patterns:
                    pattern = min(unseen_patterns)
                    orbit = {
                        tuple(pattern[action.index(index)] for index in range(6))
                        for action in triple_actions
                    }
                    unseen_patterns -= orbit
                    pattern_orbits.append(orbit)
                valid_pattern_orbits = sorted(
                    (
                        orbit
                        for orbit in pattern_orbits
                        if tuple(
                            (16 // len(orbit))
                            * sum(pattern[index] for pattern in orbit)
                            for index in range(6)
                        )
                        == (8,) * 6
                    ),
                    key=lambda orbit: (len(orbit), min(orbit)),
                )
                assert len(valid_pattern_orbits) == 6
                selected_pattern_orbit = valid_pattern_orbits[args.f20_pattern]
                if args.fiber_partition is None:
                    for block in range(5):
                        translated_patterns = []
                        for pattern in selected_pattern_orbit:
                            translated_patterns.append(
                                {
                                    tuple(
                                        sorted(
                                            (vertex + block) % 5 for vertex in triple
                                        )
                                    ): pattern[index]
                                    for index, triple in enumerate(base_triples)
                                }
                            )
                        for local_point in range(16):
                            point = 16 * block + local_point
                            solver.add(
                                z3.Or(
                                    *(
                                        z3.And(
                                            *(
                                                z3.Sum(
                                                    *(
                                                        z3.If(chosen[index], 1, 0)
                                                        for index in by_point_and_block_triple[
                                                            (point, triple)
                                                        ]
                                                    )
                                                )
                                                == count
                                                for triple, count in pattern.items()
                                            )
                                        )
                                        for pattern in translated_patterns
                                    )
                                )
                            )
                fiber_partitions = (
                    FIBER_PARTITIONS_8
                    if len(selected_pattern_orbit) == 2
                    else FIBER_PARTITIONS_4
                )
                if args.fiber_partition is not None:
                    fiber_partitions = (
                        fiber_partitions[args.fiber_partition],
                    )
                local_counts = {
                    (local_point, triple): z3.Sum(
                        *(
                            z3.If(chosen[index], 1, 0)
                            for index in by_point_and_block_triple[
                                (local_point, triple)
                            ]
                        )
                    )
                    for local_point in range(16)
                    for triple in base_triples
                }
                if args.fiber_bijection is None:
                    partition_selectors = [
                        z3.Bool(f"fiber_partition_{index}")
                        for index in range(len(fiber_partitions))
                    ]
                    solver.add(
                        z3.PbEq(
                            [(selector, 1) for selector in partition_selectors], 1
                        )
                    )
                    for selector, partition in zip(
                        partition_selectors, fiber_partitions
                    ):
                        representatives = []
                        for fiber in partition:
                            representative = fiber[0]
                            representatives.append(representative)
                            for local_point in fiber[1:]:
                                for triple in base_triples:
                                    solver.add(
                                        z3.Implies(
                                            selector,
                                            local_counts[(local_point, triple)]
                                            == local_counts[(representative, triple)],
                                        )
                                    )
                        for left, right in combinations(representatives, 2):
                            solver.add(
                                z3.Implies(
                                    selector,
                                    z3.Or(
                                        *(
                                            local_counts[(left, triple)]
                                            != local_counts[(right, triple)]
                                            for triple in base_triples
                                        )
                                    ),
                                )
                            )
                    if args.fiber_partition is not None:
                        assert len(fiber_partitions) == 1
                        partition = fiber_partitions[0]
                        pattern_list = sorted(selected_pattern_orbit)
                        solver.add(
                            z3.Or(
                                *(
                                    z3.And(
                                        *(
                                            local_counts[(fiber[0], triple)]
                                            == pattern_list[permutation[fiber_index]][
                                                triple_index
                                            ]
                                            for fiber_index, fiber in enumerate(partition)
                                            for triple_index, triple in enumerate(
                                                base_triples
                                            )
                                        )
                                    )
                                    for permutation in permutations(
                                        range(len(partition))
                                    )
                                )
                            )
                        )
                else:
                    assert len(fiber_partitions) == 1
                    partition = fiber_partitions[0]
                    pattern_list = sorted(selected_pattern_orbit)
                    bijection = list(permutations(range(len(partition))))[
                        args.fiber_bijection
                    ]
                    for fiber_index, fiber in enumerate(partition):
                        pattern = pattern_list[bijection[fiber_index]]
                        for local_point in fiber:
                            for triple_index, triple in enumerate(base_triples):
                                solver.add(
                                    local_counts[(local_point, triple)]
                                    == pattern[triple_index]
                                )
        if args.stabilizer in ("a5-star", "a5-triangle"):
            for block in range(5):
                other_blocks = [other for other in range(5) if other != block]
                incident_triples = sorted(
                    triple for triple in block_triples if block in triple
                )
                patterns = []
                for distinguished in other_blocks:
                    if args.stabilizer == "a5-star":
                        pattern = {
                            triple
                            for triple in incident_triples
                            if distinguished in triple
                        }
                    else:
                        pattern = {
                            triple
                            for triple in incident_triples
                            if distinguished not in triple
                        }
                    assert len(pattern) == 3
                    patterns.append(pattern)
                for local_point in range(16):
                    point = 16 * block + local_point
                    presence = {}
                    for triple in incident_triples:
                        indices = by_point_and_block_triple[(point, triple)]
                        solver.add(
                            z3.PbLe([(chosen[index], 1) for index in indices], 1)
                        )
                        presence[triple] = z3.Or(
                            *(chosen[index] for index in indices)
                        )
                    solver.add(
                        z3.Or(
                            *(
                                z3.And(
                                    *(
                                        presence[triple]
                                        if triple in pattern
                                        else z3.Not(presence[triple])
                                        for triple in incident_triples
                                    )
                                )
                                for pattern in patterns
                            )
                        )
                    )
            if args.a5_fiber_partition is not None:
                assert args.a5_fiber_bijection is not None
                partition = FIBER_PARTITIONS_4[args.a5_fiber_partition]
                bijection = list(permutations(range(4)))[args.a5_fiber_bijection]
                block = 0
                other_blocks = [1, 2, 3, 4]
                incident_triples = sorted(
                    triple for triple in block_triples if block in triple
                )
                for fiber_index, fiber in enumerate(partition):
                    distinguished = other_blocks[bijection[fiber_index]]
                    pattern = {
                        triple
                        for triple in incident_triples
                        if (
                            distinguished in triple
                            if args.stabilizer == "a5-star"
                            else distinguished not in triple
                        )
                    }
                    for local_point in fiber:
                        point = local_point
                        for triple in incident_triples:
                            solver.add(
                                z3.PbEq(
                                    [
                                        (chosen[index], 1)
                                        for index in by_point_and_block_triple[
                                            (point, triple)
                                        ]
                                    ],
                                    int(triple in pattern),
                                )
                            )
    for indices in by_pair.values():
        solver.add(z3.PbLe([(chosen[i], 1) for i in indices], 1))
    for pair, indices in by_pair.items():
        solver.add(triangular_edge[pair] == z3.Or(*(chosen[i] for i in indices)))

    # If one point has two T-neighbors in a fixed shadow component, those
    # neighbors must be at shadow distance at least three.  Distance one
    # would give a shadow edge a common neighbor; distance two would close a
    # C4 using the intervening shadow vertex.  Encoding this up front removes
    # the overwhelmingly common lazy-cut obstructions.
    distance_two = dict(nx.all_pairs_shortest_path_length(component, cutoff=2))
    forbidden_local_pairs = [
        (left, right)
        for left, right in combinations(range(16), 2)
        if right in distance_two[left]
    ]
    assert len(forbidden_local_pairs) == 72
    for center in range(80):
        center_block = center // 16
        for target_block in range(5):
            if target_block == center_block:
                continue
            for local_left, local_right in forbidden_local_pairs:
                left = 16 * target_block + local_left
                right = 16 * target_block + local_right
                solver.add(
                    z3.Or(
                        z3.Not(triangular_edge[tuple(sorted((center, left)))]),
                        z3.Not(triangular_edge[tuple(sorted((center, right)))]),
                    )
                )

    def adjacency(left: int, right: int) -> z3.BoolRef:
        if left // 16 == right // 16:
            return z3.BoolVal(shadow.has_edge(left, right))
        return triangular_edge[tuple(sorted((left, right)))]

    # Encode the complete obstruction, not merely the especially frequent
    # distance-two special case.  Every endpoint pair has at most one common
    # neighbor (equivalent to C4-freeness), while a prescribed shadow edge
    # has none.  Keeping the lazy checker below provides an independent
    # reconstruction check on any model returned by Z3.
    if args.encoding == "direct":
        for left, right in combinations(range(80), 2):
            common_neighbor_terms = [
                z3.And(adjacency(left, center), adjacency(right, center))
                for center in range(80)
                if center not in (left, right)
            ]
            bound = 0 if shadow.has_edge(left, right) else 1
            solver.add(
                z3.PbLe([(term, 1) for term in common_neighbor_terms], bound)
            )

    if args.backend == "kissat":
        goal = z3.Goal()
        goal.add(*solver.assertions())
        tactic = (
            z3.Then("simplify", "card2bv", "tseitin-cnf")
            if args.encoding == "lazy"
            else z3.Then("simplify", "card2bv", "tseitin-cnf")
        )
        result = tactic(goal)
        assert len(result) == 1
        base_dimacs = result[0].dimacs()
        base_lines = base_dimacs.splitlines()
        header = base_lines[0].split()
        assert header[:2] == ["p", "cnf"]
        variable_count, base_clause_count = map(int, header[2:])
        base_clauses = [
            line for line in base_lines[1:] if line and not line.startswith("c ")
        ]
        comments = [line for line in base_lines[1:] if line.startswith("c ")]
        assert len(base_clauses) == base_clause_count
        variable_by_number = {
            int(parts[1]): parts[2]
            for line in comments
            if len(parts := line.split(maxsplit=2)) == 3
        }
        number_by_variable = {name: number for number, name in variable_by_number.items()}

        def edge_variable_number(pair: tuple[int, int]) -> int:
            image_pair = pair
            while True:
                name = f"edge_{image_pair[0]}_{image_pair[1]}"
                if name in number_by_variable:
                    return number_by_variable[name]
                image_pair = tuple(sorted(map(rotation, image_pair)))
                if image_pair == pair:
                    raise AssertionError(f"eliminated edge orbit: {pair}")

        extra_clauses: list[tuple[int, ...]] = []
        extra_clause_set: set[tuple[int, ...]] = set()
        for round_index in range(args.max_rounds + 1):
            dimacs = "\n".join(
                [
                    f"p cnf {variable_count} {base_clause_count + len(extra_clauses)}",
                    *base_clauses,
                    *(" ".join(map(str, clause)) + " 0" for clause in extra_clauses),
                    *comments,
                    "",
                ]
            )
            process = subprocess.run(
                [
                    "kissat",
                    "--quiet",
                    f"--seed={args.kissat_seed}",
                    *( ["--unsat"] if args.kissat_mode == "unsat" else [] ),
                ],
                input=dimacs,
                text=True,
                capture_output=True,
            )
            if process.returncode == 20:
                print(f"UNSAT backend=kissat rounds={round_index}")
                print(
                    f"excluded_quotient={args.quotient}",
                    f"rotation_class={args.rotation_class}",
                )
                return
            if process.returncode != 10:
                raise RuntimeError(
                    f"Kissat failed with status {process.returncode}: {process.stderr}"
                )
            if args.encoding == "direct":
                raise RuntimeError("direct formula unexpectedly returned SAT")

            positive = {
                int(literal)
                for line in process.stdout.splitlines()
                if line.startswith("v ")
                for literal in line.split()[1:]
                if int(literal) > 0
            }
            line_number = {
                int(name.removeprefix("line_")): number
                for number, name in variable_by_number.items()
                if name.startswith("line_")
            }
            selected = set()
            for orbit in line_rotation_orbits:
                surviving = [line_number[index] for index in orbit if index in line_number]
                assert surviving, orbit
                values = {number in positive for number in surviving}
                assert len(values) == 1
                if values == {True}:
                    selected |= orbit
            assert len(selected) == 80, len(selected)
            triangular = nx.Graph()
            triangular.add_nodes_from(range(80))
            selected_edge_owner = {}
            for index in selected:
                for pair in combinations(lines[index], 2):
                    assert pair not in selected_edge_owner
                    selected_edge_owner[pair] = index
                    triangular.add_edge(*pair)
            candidate = nx.compose(shadow, triangular)
            bad_sets = set()
            for left, right in shadow.edges():
                for center in set(candidate[left]) & set(candidate[right]):
                    symbolic_edges = frozenset(
                        tuple(sorted(edge))
                        for edge in ((left, center), (right, center))
                        if tuple(sorted(edge)) in selected_edge_owner
                    )
                    assert symbolic_edges
                    bad_sets.add(symbolic_edges)
            for cycle in centered_c4s(candidate):
                symbolic_edges = frozenset(
                    pair
                    for edge in zip(cycle, cycle[1:] + cycle[:1])
                    if (pair := tuple(sorted(edge))) in selected_edge_owner
                )
                assert symbolic_edges
                bad_sets.add(symbolic_edges)
            if not bad_sets:
                print(f"SAT C4-free lift round={round_index}")
                return
            for symbolic_edges in bad_sets:
                orbit_edges = symbolic_edges
                while True:
                    clause = tuple(
                        sorted(
                            -edge_variable_number((left, right))
                            for left, right in orbit_edges
                        )
                    )
                    if clause not in extra_clause_set:
                        extra_clause_set.add(clause)
                        extra_clauses.append(clause)
                    orbit_edges = frozenset(
                        tuple(sorted((rotation(left), rotation(right))))
                        for left, right in orbit_edges
                    )
                    if orbit_edges == symbolic_edges:
                        break
            print(
                f"round={round_index} cuts={len(bad_sets)}",
                f"orbit_clauses={len(extra_clauses)}",
                flush=True,
            )
        raise RuntimeError(f"round limit reached: {args.max_rounds}")

    iteration = 0
    cuts = 0
    result = solver.check()
    while result == z3.sat:
        iteration += 1
        model = solver.model()
        selected = {i for i, variable in enumerate(chosen) if z3.is_true(model[variable])}
        assert len(selected) == 80
        triangular = nx.Graph()
        triangular.add_nodes_from(range(80))
        selected_edge_owner = {}
        for index in selected:
            for pair in combinations(lines[index], 2):
                assert pair not in selected_edge_owner
                selected_edge_owner[pair] = index
                triangular.add_edge(*pair)
        assert set(dict(triangular.degree()).values()) == {6}
        candidate = nx.compose(shadow, triangular)

        bad_sets = set()
        for left, right in shadow.edges():
            for center in set(candidate[left]) & set(candidate[right]):
                owners = frozenset(
                    selected_edge_owner[tuple(sorted(edge))]
                    for edge in ((left, center), (right, center))
                    if tuple(sorted(edge)) in selected_edge_owner
                )
                assert owners
                bad_sets.add(owners)
        for cycle in centered_c4s(candidate):
            cycle_edges = zip(cycle, cycle[1:] + cycle[:1])
            owners = frozenset(
                selected_edge_owner[pair]
                for edge in cycle_edges
                if (pair := tuple(sorted(edge))) in selected_edge_owner
            )
            assert owners
            bad_sets.add(owners)

        if not bad_sets:
            print(f"SAT witness iteration={iteration}")
            for index in sorted(selected):
                print("line", lines[index])
            return
        for owners in bad_sets:
            solver.add(z3.Or(*(z3.Not(chosen[index]) for index in owners)))
        cuts += len(bad_sets)
        if iteration % 10 == 0:
            print(f"iteration={iteration} cuts={cuts}", flush=True)
        result = solver.check()

    if result != z3.unsat:
        raise RuntimeError(f"solver ended without a proof: {result}")
    print(f"UNSAT iterations={iteration} cuts={cuts}")
    print(f"excluded_quotient={args.quotient}")


if __name__ == "__main__":
    main()
