#!/usr/bin/env python3
"""Probe partial-common-neighbor associators on exact q=4 controls."""

from __future__ import annotations

import argparse
import itertools
from collections import Counter

from z3 import And, Bool, If, Or, Solver, Sum, is_true, sat


Q = 4
N = Q * Q
ROOT_NEIGHBORS = set(range(1, Q + 1))


def graph_from_model(variables, model) -> list[int]:
    adjacency = [0] * N
    for (i, j), variable in variables.items():
        if is_true(model.eval(variable)):
            adjacency[i] |= 1 << j
            adjacency[j] |= 1 << i
    return adjacency


def analyze(adjacency: list[int]) -> tuple:
    common = [[adjacency[x] & adjacency[y] for y in range(N)] for x in range(N)]
    operation: list[list[int | None]] = [[None] * N for _ in range(N)]
    for x in range(N):
        for y in range(N):
            if x != y and common[x][y].bit_count() == 1:
                operation[x][y] = common[x][y].bit_length() - 1

    triangles = [
        sum(bool(adjacency[y] & (1 << z)) for y, z in itertools.combinations(
            [u for u in range(N) if adjacency[x] & (1 << u)], 2
        ))
        for x in range(N)
    ]
    at = [sum(triangles[y] for y in range(N) if adjacency[x] & (1 << y)) for x in range(N)]

    signatures = []
    for x in range(N):
        counts = Counter()
        for y in range(N):
            for z in range(N):
                xy = operation[x][y]
                yz = operation[y][z]
                left = operation[xy][z] if xy is not None else None
                right = operation[x][yz] if yz is not None else None
                if left is not None and right is not None:
                    counts["equal" if left == right else "unequal"] += 1
                elif left is not None:
                    counts["left_only"] += 1
                elif right is not None:
                    counts["right_only"] += 1
        signatures.append(tuple(counts[key] for key in ("equal", "unequal", "left_only", "right_only")))

    vertex_profile = Counter(
        (triangles[x], at[x], signatures[x], tuple(value % 4 for value in signatures[x]))
        for x in range(N)
    )
    defect_edges = [
        (x, y) for x in range(N) for y in range(x + 1, N)
        if common[x][y] == 0
    ]
    propagation = tuple(
        sum(1 for x, y in defect_edges if signatures[x][coordinate] % 4 != signatures[y][coordinate] % 4)
        for coordinate in range(4)
    )
    target_mismatch = sum(1 for x, y in defect_edges if triangles[x] % 4 != triangles[y] % 4)
    return tuple(sorted(vertex_profile.items())), propagation, target_mismatch


def main() -> None:
    global Q, N, ROOT_NEIGHBORS
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--q", type=int, default=4)
    parser.add_argument("--models", type=int, default=256)
    parser.add_argument("--timeout-ms", type=int, default=120_000)
    args = parser.parse_args()
    Q = args.q
    N = Q * Q
    ROOT_NEIGHBORS = set(range(1, Q + 1))

    solver = Solver()
    solver.set(timeout=args.timeout_ms, random_seed=850081)
    variables = {
        (i, j): Bool(f"a_{i}_{j}")
        for i in range(N) for j in range(i + 1, N)
    }

    def edge(i: int, j: int):
        if i == j:
            return False
        return variables[tuple(sorted((i, j)))]

    for vertex in range(1, N):
        solver.add(edge(0, vertex) == (vertex in ROOT_NEIGHBORS))
    for vertex in range(N):
        solver.add(Sum([If(edge(vertex, other), 1, 0) for other in range(N) if other != vertex]) == Q)
    for i, j in itertools.combinations(range(N), 2):
        solver.add(Sum([
            If(And(edge(i, k), edge(j, k)), 1, 0)
            for k in range(N) if k != i and k != j
        ]) <= 1)

    profiles = Counter()
    for model_index in range(args.models):
        result = solver.check()
        if result != sat:
            print(f"enumeration_stopped={result}; models={model_index}")
            raise SystemExit(2)
        model = solver.model()
        profiles[analyze(graph_from_model(variables, model))] += 1
        solver.add(Or([variable != model.eval(variable) for variable in variables.values()]))

    print(f"q={Q}; bounded_models={args.models}; profiles={len(profiles)}")
    for (vertices, propagation, target_mismatch), count in profiles.items():
        print(f"profile_count={count}; associator_mod4_defect_edge_mismatches={propagation}; target_t_mismatches={target_mismatch}")
        for item, multiplicity in vertices:
            print(f"  vertex=(t,At,assoc,assoc_mod4){item}; multiplicity={multiplicity}")


if __name__ == "__main__":
    main()
