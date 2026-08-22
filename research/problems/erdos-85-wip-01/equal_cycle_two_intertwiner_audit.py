#!/usr/bin/env python3
"""Search for degree-two cycle intertwiners beyond two dihedral matchings."""

from argparse import ArgumentParser
from itertools import combinations

from z3 import Bool, If, Or, Solver, Sum, sat


def solve(n: int):
    q = [[Bool(f"q_{i}_{j}") for j in range(n)] for i in range(n)]
    solver = Solver()
    for i in range(n):
        solver.add(Sum([If(q[i][j], 1, 0) for j in range(n)]) == 2)
        solver.add(Sum([If(q[j][i], 1, 0) for j in range(n)]) == 2)
    for i in range(n):
        for j in range(n):
            solver.add(
                If(q[(i - 1) % n][j], 1, 0) + If(q[(i + 1) % n][j], 1, 0)
                == If(q[i][(j - 1) % n], 1, 0) + If(q[i][(j + 1) % n], 1, 0)
            )

    maps = []
    for sign in (1, -1):
        for shift in range(n):
            maps.append(tuple((sign * i + shift) % n for i in range(n)))
    supports = set()
    for first, second in combinations(maps, 2):
        if all(first[i] != second[i] for i in range(n)):
            supports.add(tuple(tuple(sorted((first[i], second[i]))) for i in range(n)))
    for support in supports:
        solver.add(Or([q[i][j] != (j in support[i]) for i in range(n) for j in range(n)]))

    result = solver.check()
    print(f"n={n}: {result} ({len(supports)} dihedral-pair supports excluded)", flush=True)
    if result == sat:
        model = solver.model()
        for i in range(n):
            print(i, [j for j in range(n) if model.eval(q[i][j])], flush=True)


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("n", type=int, nargs="+")
    args = parser.parse_args()
    for n in args.n:
        solve(n)
