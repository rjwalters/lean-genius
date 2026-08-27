#!/usr/bin/env python3
"""Audit the coherent (2-WL) closure of q=4 boundary controls.

The closure starts only from equality and ambient adjacency.  It records
whether the resulting diagonal fibers and defect relations force more than
the rooted triangle colors that motivated the construction.
"""

from __future__ import annotations

import argparse
import itertools
from collections import Counter, defaultdict

from z3 import And, Bool, If, Or, Solver, Sum, is_true, sat


Q = 4
N = Q * Q
ROOT_NEIGHBORS = set(range(1, Q + 1))


def adjacent(adjacency: list[int], left: int, right: int) -> bool:
    return bool(adjacency[left] & (1 << right))


def stable_pair_colors(adjacency: list[int]) -> list[list[int]]:
    colors = [
        [0 if i == j else 1 if adjacent(adjacency, i, j) else 2 for j in range(N)]
        for i in range(N)
    ]
    while True:
        signatures = []
        for i in range(N):
            row = []
            for j in range(N):
                counts = Counter((colors[i][k], colors[k][j]) for k in range(N))
                row.append((colors[i][j], tuple(sorted(counts.items()))))
            signatures.append(row)
        palette = {signature for row in signatures for signature in row}
        numbering = {signature: index for index, signature in enumerate(sorted(palette))}
        refined = [[numbering[signatures[i][j]] for j in range(N)] for i in range(N)]
        if refined == colors:
            return colors
        colors = refined


def profile(adjacency: list[int]) -> tuple:
    common = [[(adjacency[i] & adjacency[j]).bit_count() for j in range(N)] for i in range(N)]
    triangles = [
        sum(adjacent(adjacency, y, z) for y, z in itertools.combinations(
            [u for u in range(N) if adjacent(adjacency, x, u)], 2
        ))
        for x in range(N)
    ]
    at = [sum(triangles[y] for y in range(N) if adjacent(adjacency, x, y)) for x in range(N)]
    colors = stable_pair_colors(adjacency)
    diagonal_fibers: dict[int, list[int]] = defaultdict(list)
    for x in range(N):
        diagonal_fibers[colors[x][x]].append(x)

    fiber_data = tuple(sorted(
        (
            len(vertices),
            tuple(sorted(Counter(triangles[x] for x in vertices).items())),
            tuple(sorted(Counter(at[x] for x in vertices).items())),
        )
        for vertices in diagonal_fibers.values()
    ))

    # A coherent color cannot mix different ordered-pair statistics.  Record
    # explicitly whether defect colors join distinct diagonal fibers and
    # whether their endpoint triangle data are already encoded by the color.
    defect_color_data: dict[int, Counter[tuple[int, int, int, int]]] = defaultdict(Counter)
    for x in range(N):
        for y in range(N):
            if x != y and common[x][y] == 0:
                defect_color_data[colors[x][y]][
                    (colors[x][x], colors[y][y], triangles[x], triangles[y])
                ] += 1
    defect_data = tuple(sorted(
        (sum(values.values()), tuple(sorted(values.items())))
        for values in defect_color_data.values()
    ))
    return (len({c for row in colors for c in row}), fiber_data, defect_data)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--models", type=int, default=256)
    parser.add_argument("--timeout-ms", type=int, default=120_000)
    args = parser.parse_args()

    solver = Solver()
    solver.set(timeout=args.timeout_ms, random_seed=850080)
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

    profiles: Counter[tuple] = Counter()
    for model_index in range(args.models):
        result = solver.check()
        if result != sat:
            print(f"enumeration_stopped={result}; models={model_index}")
            raise SystemExit(2)
        model = solver.model()
        adjacency = [0] * N
        for (i, j), variable in variables.items():
            if is_true(model.eval(variable)):
                adjacency[i] |= 1 << j
                adjacency[j] |= 1 << i
        profiles[profile(adjacency)] += 1
        solver.add(Or([variable != model.eval(variable) for variable in variables.values()]))

    print(f"bounded_models={args.models}; closure_profiles={len(profiles)}")
    for (rank, fibers, defect_data), count in profiles.items():
        print(f"model_profile_count={count}; coherent_rank={rank}")
        print(f"diagonal_fibers=(size,t_hist,At_hist): {fibers}")
        print(f"defect_colors=(size,((source_fiber,target_fiber,t_x,t_y),count)): {defect_data}")


if __name__ == "__main__":
    main()
