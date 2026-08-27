#!/usr/bin/env python3
"""Rooted C5/remote-edge incidence probe for the q=4 calibration corpus.

For each root x this computes:
* t_x, the number of triangles through x;
* B_x, triangles not through x meeting N(x) in exactly one vertex;
* R_x, the vertices outside the closed two-ball, and E_x=e_A(R_x);
* C_x, unoriented simple 5-cycles through x;
* the GF(2) incidence matrix between E_x and C_x.

The purpose is to test whether E_x-C_x+3t_x has a genuine boundary-rank or
pairing explanation.  A useful link-complex mechanism should expose more than
the already-known cardinality residue.
"""

from __future__ import annotations

import argparse
import itertools
from collections import Counter

from z3 import And, Bool, If, Or, Solver, Sum, is_true, sat


Q = 4
N = Q * Q
ROOT_NEIGHBORS = set(range(1, Q + 1))


def adjacent(adjacency: list[int], left: int, right: int) -> bool:
    return bool(adjacency[left] & (1 << right))


def neighbors(adjacency: list[int], vertex: int) -> list[int]:
    bits = adjacency[vertex]
    return [other for other in range(N) if bits & (1 << other)]


def rooted_c5s(adjacency: list[int], root: int) -> set[tuple[int, int, int, int]]:
    cycles: set[tuple[int, int, int, int]] = set()
    for first in neighbors(adjacency, root):
        for second in neighbors(adjacency, first):
            if second == root:
                continue
            for third in neighbors(adjacency, second):
                if third in (root, first):
                    continue
                for fourth in neighbors(adjacency, third):
                    if fourth in (root, first, second) or not adjacent(adjacency, fourth, root):
                        continue
                    forward = (first, second, third, fourth)
                    reverse = tuple(reversed(forward))
                    cycles.add(min(forward, reverse))
    return cycles


def gf2_rank(rows: list[int]) -> int:
    basis: dict[int, int] = {}
    for row in rows:
        value = row
        while value:
            pivot = value.bit_length() - 1
            if pivot in basis:
                value ^= basis[pivot]
            else:
                basis[pivot] = value
                break
    return len(basis)


def root_profile(adjacency: list[int], root: int) -> tuple:
    root_neighbors = set(neighbors(adjacency, root))
    triangles = [
        triple
        for triple in itertools.combinations(range(N), 3)
        if all(adjacent(adjacency, left, right) for left, right in itertools.combinations(triple, 2))
    ]
    triangle_degree = sum(root in triple for triple in triangles)
    external_triangles = sum(
        root not in triple and len(root_neighbors.intersection(triple)) == 1
        for triple in triangles
    )
    second_layer = {
        vertex
        for vertex in range(N)
        if vertex != root
        and vertex not in root_neighbors
        and len(root_neighbors.intersection(neighbors(adjacency, vertex))) == 1
    }
    remote = set(range(N)) - {root} - root_neighbors - second_layer
    remote_edges = [
        pair
        for pair in itertools.combinations(sorted(remote), 2)
        if adjacent(adjacency, *pair)
    ]
    cycles = sorted(rooted_c5s(adjacency, root))
    incidence_rows = []
    remote_degrees = []
    for edge in remote_edges:
        row = 0
        for cycle_index, cycle in enumerate(cycles):
            vertices = (root,) + cycle
            cycle_edges = {
                tuple(sorted((vertices[index], vertices[(index + 1) % 5])))
                for index in range(5)
            }
            if edge in cycle_edges:
                row |= 1 << cycle_index
        incidence_rows.append(row)
        remote_degrees.append(row.bit_count())
    cycle_degrees = []
    for cycle_index in range(len(cycles)):
        cycle_degrees.append(sum(bool(row & (1 << cycle_index)) for row in incidence_rows))
    target = (len(remote_edges) - len(cycles) + 3 * triangle_degree) % 4
    return (
        triangle_degree,
        external_triangles,
        len(remote),
        len(remote_edges),
        len(cycles),
        target,
        gf2_rank(incidence_rows),
        tuple(sorted(Counter(remote_degrees).items())),
        tuple(sorted(Counter(cycle_degrees).items())),
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--models", type=int, default=256)
    parser.add_argument("--timeout-ms", type=int, default=120_000)
    args = parser.parse_args()

    solver = Solver()
    solver.set(timeout=args.timeout_ms, random_seed=850077)
    variables = {
        (left, right): Bool(f"a_{left}_{right}")
        for left in range(N)
        for right in range(left + 1, N)
    }

    def edge(left: int, right: int):
        if left == right:
            return False
        return variables[tuple(sorted((left, right)))]

    for vertex in range(1, N):
        solver.add(edge(0, vertex) == (vertex in ROOT_NEIGHBORS))
    for vertex in range(N):
        solver.add(
            Sum([If(edge(vertex, other), 1, 0) for other in range(N) if other != vertex])
            == Q
        )
    for left, right in itertools.combinations(range(N), 2):
        solver.add(
            Sum(
                [
                    If(And(edge(left, middle), edge(right, middle)), 1, 0)
                    for middle in range(N)
                    if middle != left and middle != right
                ]
            )
            <= 1
        )

    profiles: Counter[tuple] = Counter()
    for model_index in range(args.models):
        result = solver.check()
        if result != sat:
            print(f"enumeration_stopped={result}; models={model_index}")
            raise SystemExit(2)
        model = solver.model()
        adjacency = [0] * N
        for (left, right), variable in variables.items():
            if is_true(model.eval(variable)):
                adjacency[left] |= 1 << right
                adjacency[right] |= 1 << left
        profiles.update(root_profile(adjacency, root) for root in range(N))
        solver.add(Or([variable != model.eval(variable) for variable in variables.values()]))

    print(f"bounded_models={args.models}; rooted_samples={args.models * N}")
    print(
        "profile=(t,B,|R|,E,C5,target_mod4,rank_F2,remote_degree_hist,cycle_degree_hist)"
    )
    for profile, count in sorted(profiles.items()):
        print(f"count={count}: {profile}")


if __name__ == "__main__":
    main()
