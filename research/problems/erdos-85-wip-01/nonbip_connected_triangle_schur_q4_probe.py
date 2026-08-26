#!/usr/bin/env python3
"""Bounded q=4 probe of the triangle-hypergraph Schur complement."""

from __future__ import annotations

import argparse
import itertools
from collections import Counter

import sympy
from z3 import And, Bool, If, Or, Solver, Sum, is_true, sat


Q = 4
N = Q * Q
ROOT_NEIGHBORS = set(range(1, Q + 1))


def triangle_schur_profile(edges: list[tuple[int, int]]) -> tuple[int, ...]:
    adjacency = sympy.zeros(N)
    for left, right in edges:
        adjacency[left, right] = adjacency[right, left] = 1
    triangles = [
        triple
        for triple in itertools.combinations(range(N), 3)
        if all(adjacency[left, right] for left, right in itertools.combinations(triple, 2))
    ]
    incidence = sympy.zeros(N, len(triangles))
    triangle_degrees = [0] * N
    for column, triple in enumerate(triangles):
        for vertex in triple:
            incidence[vertex, column] = 1
            triangle_degrees[vertex] += 1

    remainder = adjacency.copy()
    for triple in triangles:
        for left, right in itertools.combinations(triple, 2):
            remainder[left, right] = remainder[right, left] = 0
    core = remainder - sympy.diag(*triangle_degrees)
    assert adjacency == core + incidence * incidence.T

    rank_adjacency = adjacency.rank()
    rank_core = core.rank()
    if rank_core < N:
        return (len(triangles), rank_adjacency, rank_core, -1, -1)
    schur = sympy.eye(len(triangles)) + incidence.T * core.inv() * incidence
    ones = sympy.ones(len(triangles), 1)
    return (
        len(triangles),
        rank_adjacency,
        rank_core,
        schur.rank(),
        int(schur * ones == sympy.zeros(len(triangles), 1)),
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--models", type=int, default=256)
    parser.add_argument("--timeout-ms", type=int, default=120_000)
    args = parser.parse_args()

    solver = Solver()
    solver.set(timeout=args.timeout_ms, random_seed=850073)
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
                    If(And(edge(left, common), edge(right, common)), 1, 0)
                    for common in range(N)
                    if common != left and common != right
                ]
            )
            <= 1
        )

    profiles: Counter[tuple[int, ...]] = Counter()
    for index in range(args.models):
        result = solver.check()
        if result != sat:
            print(f"enumeration_stopped={result}; models={index}")
            break
        model = solver.model()
        edges = [
            pair for pair, variable in variables.items() if is_true(model.eval(variable))
        ]
        profile = triangle_schur_profile(edges)
        profiles[profile] += 1
        # Stop immediately on either decisive falsifier.
        if profile[1] == N or (profile[2] == N and profile[4] == 0):
            print(f"falsifier_model={index}; profile={profile}; edges={edges}")
            raise SystemExit(1)
        solver.add(Or([variable != model.eval(variable) for variable in variables.values()]))
    else:
        print(f"bounded_models={args.models}")

    print("profile=(triangles,rank_A,rank_core,rank_S,S_one_zero)")
    for profile, count in sorted(profiles.items()):
        print(f"{profile}: {count}")


if __name__ == "__main__":
    main()
