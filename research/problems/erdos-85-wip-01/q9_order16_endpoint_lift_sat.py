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
from itertools import combinations, product
from pathlib import Path

import networkx as nx
import z3


EXPECTED_SHA256 = "4bac89beec1465265318266117c38a2c1680e73a21efd322411207cef5313088"
BLOCK_TRIPLES = (
    (0, 1, 2),
    (0, 1, 4),
    (0, 3, 4),
    (1, 2, 3),
    (2, 3, 4),
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("census", type=Path)
    parser.add_argument("--backend", choices=("kissat", "z3"), default="kissat")
    parser.add_argument("--rotation-class", type=int)
    parser.add_argument("--seed-orbit", type=int)
    parser.add_argument("--all", action="store_true")
    args = parser.parse_args()
    raw = args.census.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_SHA256
    component = component_ordinal_4(raw)
    shadow = shadow_product(component)

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
                ]
                if seed_orbit is not None:
                    command.extend(("--seed-orbit", str(seed_orbit)))
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
        print("excluded_endpoint_action_patterns=4")
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
    for block_triple in BLOCK_TRIPLES:
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

    for index, line in enumerate(lines):
        image = tuple(sorted(rotation(point) for point in line))
        solver.add(chosen[index] == chosen[line_to_index[image]])
    for block_triple in BLOCK_TRIPLES:
        solver.add(z3.PbEq([(chosen[i], 1) for i in by_block_triple[block_triple]], 16))
        for block in block_triple:
            for local_point in range(16):
                point = 16 * block + local_point
                solver.add(
                    z3.PbEq(
                        [
                            (chosen[i], 1)
                            for i in by_point_and_block_triple[(point, block_triple)]
                        ],
                        1,
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
    for left, right in combinations(range(80), 2):
        common_neighbor_terms = [
            z3.And(adjacency(left, center), adjacency(right, center))
            for center in range(80)
            if center not in (left, right)
        ]
        bound = 0 if shadow.has_edge(left, right) else 1
        solver.add(z3.PbLe([(term, 1) for term in common_neighbor_terms], bound))

    if args.backend == "kissat":
        goal = z3.Goal()
        goal.add(*solver.assertions())
        result = z3.Then("simplify", "card2bv", "tseitin-cnf")(goal)
        assert len(result) == 1
        process = subprocess.run(
            ["kissat", "--quiet"],
            input=result[0].dimacs(),
            text=True,
            capture_output=True,
        )
        if process.returncode == 20:
            print("UNSAT backend=kissat")
            print(f"excluded_rotation_class={args.rotation_class}")
            return
        if process.returncode == 10:
            raise RuntimeError(
                "Kissat found SAT; rerun with --backend z3 to reconstruct the model"
            )
        raise RuntimeError(
            f"Kissat failed with status {process.returncode}: {process.stderr}"
        )

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
    print("excluded_endpoint_action_patterns=4")


if __name__ == "__main__":
    main()
