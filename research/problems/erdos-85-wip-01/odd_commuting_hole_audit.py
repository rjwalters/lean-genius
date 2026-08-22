#!/usr/bin/env python3
"""Exact audit for odd bipartite two-factors commuting with C_(2n)."""

from argparse import ArgumentParser
from z3 import If, Or, Solver, Sum, sat


def solve(n: int):
    q = [[__import__("z3").Bool(f"q_{i}_{j}") for j in range(n)] for i in range(n)]
    s = Solver()
    for i in range(n):
        s.add(Sum([If(q[i][j], 1, 0) for j in range(n)]) == 2)
        s.add(Sum([If(q[j][i], 1, 0) for j in range(n)]) == 2)
        # The long cycle has cross-block R with R[i,i] = R[i,i-1] = 1.
        s.add(q[i][i] == False, q[i][(i - 1) % n] == False)
    # Q R^T = R Q^T, entrywise.
    for i in range(n):
        for j in range(n):
            s.add(
                If(q[i][j], 1, 0) + If(q[i][(j - 1) % n], 1, 0)
                == If(q[j][i], 1, 0) + If(q[j][(i - 1) % n], 1, 0)
            )
    # Exclude every symmetric rotation-circulant support {i+t,i-1-t}.
    for t in range(n):
        s.add(Or([q[i][j] != (j in {(i + t) % n, (i - 1 - t) % n})
                  for i in range(n) for j in range(n)]))
    result = s.check()
    print(f"n={n}: {result}")
    if result == sat:
        m = s.model()
        for i in range(n):
            print(i, [j for j in range(n) if m.eval(q[i][j])])


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("n", type=int, nargs="+")
    args = parser.parse_args()
    for n in args.n:
        solve(n)
