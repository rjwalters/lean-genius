#!/usr/bin/env python3
"""Ward-test the external triangle-incidence code on q=4 controls.

Let H be vertex-by-triangle incidence and C=A*H-2H.  C is a 0/1 matrix:
C[x,tau]=1 exactly when x is outside tau and adjacent to one vertex of tau.
This probe forms generators C_x+C_y over F2 for every defect edge xy and
checks the two elementary Ward conditions for their span to be doubly even:
each generator has weight divisible by four, and every generator pair has even
intersection.  Failure on q=4 cuts the universal code proposal; success is
calibration only.
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


def triangle_code_profile(adjacency: list[int]) -> tuple:
    triangles = [
        triple
        for triple in itertools.combinations(range(N), 3)
        if all(adjacent(adjacency, left, right) for left, right in itertools.combinations(triple, 2))
    ]
    triangle_degree = [sum(vertex in triple for triple in triangles) for vertex in range(N)]
    common = [
        [
            (adjacency[left] & adjacency[right]).bit_count()
            for right in range(N)
        ]
        for left in range(N)
    ]
    rows = []
    for vertex in range(N):
        row = 0
        for index, triple in enumerate(triangles):
            if vertex not in triple and sum(adjacent(adjacency, vertex, member) for member in triple) == 1:
                row |= 1 << index
        rows.append(row)
    generators = []
    edge_profiles: Counter[tuple[int, ...]] = Counter()
    for left, right in itertools.combinations(range(N), 2):
        if common[left][right] != 0:
            continue
        generator = rows[left] ^ rows[right]
        intersection = (rows[left] & rows[right]).bit_count()
        profile = (
            int(adjacent(adjacency, left, right)),
            triangle_degree[left],
            triangle_degree[right],
            rows[left].bit_count(),
            rows[right].bit_count(),
            intersection,
            generator.bit_count(),
        )
        edge_profiles[profile] += 1
        generators.append(generator)
    bad_weights = sum(generator.bit_count() % 4 != 0 for generator in generators)
    bad_pairs = sum(
        (left & right).bit_count() % 2 != 0
        for left, right in itertools.combinations(generators, 2)
    )
    return (
        len(triangles),
        tuple(sorted(edge_profiles.items())),
        len(generators),
        bad_weights,
        bad_pairs,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--models", type=int, default=256)
    parser.add_argument("--timeout-ms", type=int, default=120_000)
    args = parser.parse_args()

    solver = Solver()
    solver.set(timeout=args.timeout_ms, random_seed=850078)
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
        profiles[triangle_code_profile(adjacency)] += 1
        solver.add(Or([variable != model.eval(variable) for variable in variables.values()]))

    print(f"bounded_models={args.models}")
    for profile, count in profiles.items():
        triangle_count, edge_profiles, generator_count, bad_weights, bad_pairs = profile
        print(f"model_profile_count={count}; triangles={triangle_count}; generators={generator_count}")
        print(f"bad_generator_weights_mod4={bad_weights}; bad_generator_pair_intersections_mod2={bad_pairs}")
        print("edge_profile=((Axy,t_x,t_y,B_x,B_y,|CxInterCy|,wt(Cx+C_y)), count)")
        for entry in edge_profiles:
            print(entry)


if __name__ == "__main__":
    main()
