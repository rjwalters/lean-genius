#!/usr/bin/env python3
"""Test local cyclic embeddability of a minimum reciprocal signed trade.

This deliberately does not assert that either signed half extends to a full
reciprocal exact-hit code.  A SAT result therefore cuts off a purely local
argument; it is not a witness to a physical trade between two full codes.
"""

from __future__ import annotations

import argparse
from itertools import combinations

import z3


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int, nargs="?", default=8)
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--support", type=int, default=8)
    parser.add_argument(
        "--internal-caps", action="store_true",
        help=("require each signed half to satisfy the same-difference "
              "common-neighbor cap inside the changed support"))
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    args = parser.parse_args()

    q = args.q
    n = args.support
    holes = {args.a % q, (-1 - args.a) % q}
    allowed = sorted(set(range(q)) - holes)
    solver = z3.Solver()
    solver.set(timeout=args.timeout_ms)

    row = [z3.Int(f"row_{i}") for i in range(n)]
    col = [z3.Int(f"col_{i}") for i in range(n)]
    for i in range(n):
        solver.add(0 <= row[i], row[i] < q, 0 <= col[i], col[i] < q)
        solver.add(z3.Or([(col[i] - row[i]) % q == t
                          for t in allowed]))
    solver.add(row[0] == 0)  # simultaneous row/column translation symmetry
    for i, j in combinations(range(n), 2):
        solver.add(z3.Or(row[i] != row[j], col[i] != col[j]))

    minus: dict[tuple[int, int], z3.BoolRef] = {}
    plus: dict[tuple[int, int], z3.BoolRef] = {}

    def signed_edge(table: dict[tuple[int, int], z3.BoolRef],
                    i: int, j: int) -> z3.BoolRef:
        if i == j:
            return z3.BoolVal(False)
        key = (min(i, j), max(i, j))
        if key not in table:
            table[key] = z3.Bool(
                f"{'minus' if table is minus else 'plus'}_{key[0]}_{key[1]}")
        return table[key]

    for i, j in combinations(range(n), 2):
        m = signed_edge(minus, i, j)
        p = signed_edge(plus, i, j)
        solver.add(z3.Not(z3.And(m, p)))
        changed = z3.Or(m, p)
        # A source cell (row,col) omits target rows col,col+1 and target
        # columns row,row-1.  A reciprocal edge must be admissible in both
        # directions.
        solver.add(z3.Implies(changed, z3.And(
            row[j] != col[i], row[j] != (col[i] + 1) % q,
            col[j] != row[i], col[j] != (row[i] - 1) % q,
            row[i] != col[j], row[i] != (col[j] + 1) % q,
            col[i] != row[j], col[i] != (row[j] - 1) % q)))

    for i in range(n):
        minus_degree = z3.Sum([
            z3.If(signed_edge(minus, i, j), 1, 0)
            for j in range(n) if j != i])
        plus_degree = z3.Sum([
            z3.If(signed_edge(plus, i, j), 1, 0)
            for j in range(n) if j != i])
        solver.add(minus_degree == plus_degree, minus_degree >= 2)
        for value in range(q):
            solver.add(z3.Sum([
                z3.If(z3.And(signed_edge(minus, i, j), row[j] == value), 1, 0)
                for j in range(n) if j != i]) == z3.Sum([
                z3.If(z3.And(signed_edge(plus, i, j), row[j] == value), 1, 0)
                for j in range(n) if j != i]))

    if args.internal_caps:
        for i, j in combinations(range(n), 2):
            same_difference = (col[i] - row[i]) % q == (col[j] - row[j]) % q
            for table in (minus, plus):
                common_neighbors = z3.Sum([
                    z3.If(z3.And(signed_edge(table, i, k),
                                 signed_edge(table, j, k)), 1, 0)
                    for k in range(n) if k != i and k != j])
                solver.add(z3.Implies(same_difference,
                                      common_neighbors <= 1))
            solver.add(z3.Sum([
                z3.If(z3.And(signed_edge(minus, i, j), col[j] == value), 1, 0)
                for j in range(n) if j != i]) == z3.Sum([
                z3.If(z3.And(signed_edge(plus, i, j), col[j] == value), 1, 0)
                for j in range(n) if j != i]))

    result = solver.check()
    print(f"q={q} a={args.a % q} support={n} "
          f"internal_caps={args.internal_caps}: {result}")
    if result != z3.sat:
        return
    model = solver.model()
    cells = [(model.eval(row[i]).as_long(), model.eval(col[i]).as_long())
             for i in range(n)]
    minus_edges = [pair for pair, variable in minus.items()
                   if z3.is_true(model.eval(variable, model_completion=True))]
    plus_edges = [pair for pair, variable in plus.items()
                  if z3.is_true(model.eval(variable, model_completion=True))]
    print(f"  cells={cells}")
    print(f"  differences={[(c - r) % q for r, c in cells]}")
    print(f"  minus={minus_edges}")
    print(f"  plus={plus_edges}")


if __name__ == "__main__":
    main()
