#!/usr/bin/env python3
"""Search a closed signed trade on a prescribed number of cyclic cells."""

from __future__ import annotations

import argparse
from itertools import combinations

import z3


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("support", type=int)
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--require-rank-drop", action="store_true",
        help="add relaxed unchanged fibre loads and require fewer zero loads")
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    args = parser.parse_args()
    q, n = args.q, args.support
    holes = {args.a % q, (-1 - args.a) % q}
    differences = tuple(t for t in range(q) if t not in holes)

    solver = z3.Solver()
    solver.set(timeout=args.timeout_ms)
    base = [z3.Int(f"x_{i}") for i in range(n)]
    fibre = [z3.Int(f"t_{i}") for i in range(n)]
    for i in range(n):
        solver.add(base[i] >= 0, base[i] < q)
        solver.add(z3.Or([fibre[i] == t for t in differences]))
    solver.add(base[0] == 0)
    for i, j in combinations(range(n), 2):
        solver.add(z3.Or(base[i] != base[j], fibre[i] != fibre[j]))

    minus: dict[tuple[int, int], z3.BoolRef] = {}
    plus: dict[tuple[int, int], z3.BoolRef] = {}
    for i, j in combinations(range(n), 2):
        minus[i, j] = z3.Bool(f"minus_{i}_{j}")
        plus[i, j] = z3.Bool(f"plus_{i}_{j}")
        solver.add(z3.Not(z3.And(minus[i, j], plus[i, j])))
        used = z3.Or(minus[i, j], plus[i, j])

        def admissible(source: int, target: int) -> z3.BoolRef:
            row = base[target]
            column = (base[target] + fibre[target]) % q
            return z3.And(
                row != (base[source] + fibre[source]) % q,
                row != (base[source] + fibre[source] + 1) % q,
                column != base[source],
                column != (base[source] - 1) % q)

        solver.add(z3.Implies(
            used, z3.And(admissible(i, j), admissible(j, i))))

    def edge(family: dict[tuple[int, int], z3.BoolRef],
             i: int, j: int) -> z3.BoolRef:
        return family[min(i, j), max(i, j)]

    sign_degree: dict[int, z3.ArithRef] = {}
    for i in range(n):
        minus_degree = z3.Sum([
            z3.If(edge(minus, i, j), 1, 0) for j in range(n) if j != i])
        plus_degree = z3.Sum([
            z3.If(edge(plus, i, j), 1, 0) for j in range(n) if j != i])
        solver.add(minus_degree == plus_degree, minus_degree >= 2)
        sign_degree[i] = minus_degree
        for value in range(q):
            solver.add(z3.Sum([
                z3.If(z3.And(edge(minus, i, j), base[j] == value), 1, 0)
                for j in range(n) if j != i]) == z3.Sum([
                z3.If(z3.And(edge(plus, i, j), base[j] == value), 1, 0)
                for j in range(n) if j != i]))
            solver.add(z3.Sum([
                z3.If(z3.And(edge(minus, i, j),
                             (base[j] + fibre[j]) % q == value), 1, 0)
                for j in range(n) if j != i]) == z3.Sum([
                z3.If(z3.And(edge(plus, i, j),
                             (base[j] + fibre[j]) % q == value), 1, 0)
                for j in range(n) if j != i]))

    old_zero_total = None
    new_zero_total = None
    if args.require_rank_drop:
        old_zeros = []
        new_zeros = []
        for i in range(n):
            unchanged = {
                u: z3.Int(f"unchanged_{i}_{u}") for u in differences
            }
            for value in unchanged.values():
                solver.add(value >= 0, value <= q)
            solver.add(z3.Sum(list(unchanged.values())) ==
                       (q - 2) - sign_degree[i])
            for u in differences:
                old_load = unchanged[u] + z3.Sum([
                    z3.If(z3.And(edge(minus, i, j), fibre[j] == u), 1, 0)
                    for j in range(n) if j != i])
                new_load = unchanged[u] + z3.Sum([
                    z3.If(z3.And(edge(plus, i, j), fibre[j] == u), 1, 0)
                    for j in range(n) if j != i])
                old_zeros.append(z3.If(old_load == 0, 1, 0))
                new_zeros.append(z3.If(new_load == 0, 1, 0))
        old_zero_total = z3.Sum(old_zeros)
        new_zero_total = z3.Sum(new_zeros)
        solver.add(new_zero_total < old_zero_total)

    result = solver.check()
    print(f"q={q} a={args.a % q} support={n}: {result}")
    if result != z3.sat:
        return
    model = solver.model()
    cells = [(model.eval(base[i]).as_long(), model.eval(fibre[i]).as_long())
             for i in range(n)]
    print(f"  cells={cells}")
    if old_zero_total is not None and new_zero_total is not None:
        print(f"  relaxed_rank={model.eval(old_zero_total)} -> "
              f"{model.eval(new_zero_total)}")
    for name, family in (("minus", minus), ("plus", plus)):
        selected = [pair for pair, variable in family.items()
                    if z3.is_true(model.eval(variable))]
        print(f"  {name}={selected}")


if __name__ == "__main__":
    main()
