#!/usr/bin/env python3
"""Test the canonical cross-star parity voltage on q=4 controls.

For a defect edge xy, N_A(x) and N_A(y) are disjoint and the ambient edges
between them form a matching.  Its cardinality is (A^3)[x,y].  Reduce this
cardinality modulo two as a Z/2 voltage on D.  A vertex potential (and hence a
split double cover capable of propagating rooted data) exists exactly when the
signed defect graph is balanced: every D-cycle has zero voltage sum.
"""

from __future__ import annotations

import argparse
import itertools
from collections import Counter, deque

from z3 import And, Bool, If, Or, Solver, Sum, is_true, sat


Q = 4
N = Q * Q
ROOT_NEIGHBORS = set(range(1, Q + 1))


def adjacent(adjacency: list[int], left: int, right: int) -> bool:
    return bool(adjacency[left] & (1 << right))


def triangle_degree(adjacency: list[int], root: int) -> int:
    star = [vertex for vertex in range(N) if adjacent(adjacency, root, vertex)]
    return sum(adjacent(adjacency, left, right) for left, right in itertools.combinations(star, 2))


def model_profile(adjacency: list[int]) -> tuple:
    common = [
        [(adjacency[left] & adjacency[right]).bit_count() for right in range(N)]
        for left in range(N)
    ]
    defect_neighbors = [
        [right for right in range(N) if right != left and common[left][right] == 0]
        for left in range(N)
    ]
    triangles = [triangle_degree(adjacency, vertex) for vertex in range(N)]
    voltage: dict[tuple[int, int], int] = {}
    edge_profiles: Counter[tuple[int, ...]] = Counter()
    for left, right in itertools.combinations(range(N), 2):
        if common[left][right] != 0:
            continue
        cross = sum(
            adjacent(adjacency, u, v)
            for u in range(N)
            if adjacent(adjacency, left, u)
            for v in range(N)
            if adjacent(adjacency, right, v)
        )
        bit = cross % 2
        voltage[left, right] = voltage[right, left] = bit
        edge_profiles[(int(adjacent(adjacency, left, right)), triangles[left], triangles[right], cross, bit)] += 1

    potential: dict[int, int] = {}
    component_profiles = []
    conflicts = 0
    for start in range(N):
        if start in potential:
            continue
        potential[start] = 0
        component = []
        queue = deque([start])
        while queue:
            vertex = queue.popleft()
            component.append(vertex)
            for other in defect_neighbors[vertex]:
                expected = potential[vertex] ^ voltage[vertex, other]
                if other in potential:
                    if potential[other] != expected:
                        conflicts += 1
                else:
                    potential[other] = expected
                    queue.append(other)
        triangle_offsets = {potential[vertex] ^ (triangles[vertex] % 2) for vertex in component}
        component_profiles.append(
            (
                len(component),
                tuple(sorted(Counter(potential[vertex] for vertex in component).items())),
                tuple(sorted(Counter(triangles[vertex] for vertex in component).items())),
                tuple(sorted(triangle_offsets)),
            )
        )
    return (
        tuple(sorted(edge_profiles.items())),
        conflicts,
        tuple(sorted(component_profiles)),
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--models", type=int, default=256)
    parser.add_argument("--timeout-ms", type=int, default=120_000)
    args = parser.parse_args()

    solver = Solver()
    solver.set(timeout=args.timeout_ms, random_seed=850079)
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
        profiles[model_profile(adjacency)] += 1
        solver.add(Or([variable != model.eval(variable) for variable in variables.values()]))

    print(f"bounded_models={args.models}")
    for (edge_profiles, conflicts, component_profiles), count in profiles.items():
        print(f"model_profile_count={count}; voltage_conflicts={conflicts}")
        print("edge_profile=((Axy,t_x,t_y,cross_star_edges,voltage),count)")
        for profile in edge_profiles:
            print(profile)
        print(f"components=(size,potential_hist,t_hist,potential_xor_tParity_values): {component_profiles}")


if __name__ == "__main__":
    main()
