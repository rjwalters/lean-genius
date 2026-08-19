#!/usr/bin/env python3
"""Direct SAT probe for the graph-free SIZE-TWO-EIGENLINE(q) object.

Vertices are the allowed cells (x,y), with y-x outside the two holes
{a,-1-a}.  We ask directly for a simple graph satisfying the exact row and
column hit laws and the common-neighbour cap.  By the reconstruction theorems
this is equivalent to an exact reciprocal permutation code, but the Boolean
edge encoding is substantially smaller than the permutation encoding.
"""

from __future__ import annotations

import argparse
from itertools import combinations

import z3


def build(q: int, a: int, *, rows: bool = True, columns: bool = True,
          c4_pair_mode: str = "all") -> tuple[z3.Solver, list[tuple[int, int]], dict[tuple[int, int], z3.BoolRef]]:
    holes = {a % q, (-1 - a) % q}
    vertices = [(x, y) for x in range(q) for y in range(q) if (y - x) % q not in holes]
    index = {v: i for i, v in enumerate(vertices)}
    edge = {(i, j): z3.Bool(f"e_{i}_{j}") for i, j in combinations(range(len(vertices)), 2)}

    def adj(i: int, j: int) -> z3.BoolRef:
        if i == j:
            return z3.BoolVal(False)
        return edge[min(i, j), max(i, j)]

    solver = z3.Solver()

    # Exact row and column hits.  Zero fibers are asserted too: they provide
    # cheap unit propagation before the C4 constraints are introduced.
    for i, (x, y) in enumerate(vertices):
        if rows:
            for row in range(q):
                want = 0 if row in {y, (y + 1) % q} else 1
                solver.add(z3.PbEq([(adj(i, index[row, col]), 1)
                                    for col in range(q) if (row, col) in index], want))
        if columns:
            for col in range(q):
                want = 0 if col in {x, (x - 1) % q} else 1
                solver.add(z3.PbEq([(adj(i, index[row, col]), 1)
                                    for row in range(q) if (row, col) in index], want))

    # C4-free is exactly: distinct vertices have at most one common neighbor.
    if c4_pair_mode != "none":
        for i, j in combinations(range(len(vertices)), 2):
            if c4_pair_mode == "same-row" and vertices[i][0] != vertices[j][0]:
                continue
            if c4_pair_mode == "same-column" and vertices[i][1] != vertices[j][1]:
                continue
            if c4_pair_mode == "same-difference" and \
                    (vertices[i][1] - vertices[i][0]) % q != \
                    (vertices[j][1] - vertices[j][0]) % q:
                continue
            solver.add(z3.PbLe([(z3.And(adj(i, k), adj(j, k)), 1)
                                for k in range(len(vertices)) if k not in {i, j}], 1))

    return solver, vertices, edge


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    parser.add_argument("--no-rows", action="store_true")
    parser.add_argument("--no-columns", action="store_true")
    parser.add_argument("--no-c4", action="store_true")
    parser.add_argument("--c4-pair-mode",
        choices=["all", "same-row", "same-column", "same-difference"],
        default="all")
    args = parser.parse_args()
    solver, vertices, edge = build(args.q, args.a,
        rows=not args.no_rows, columns=not args.no_columns,
        c4_pair_mode="none" if args.no_c4 else args.c4_pair_mode)
    solver.set(timeout=args.timeout_ms)
    result = solver.check()
    print(f"q={args.q} a={args.a % args.q}: {result}")
    if result == z3.sat:
        model = solver.model()
        chosen = [(vertices[i], vertices[j]) for (i, j), var in edge.items()
                  if z3.is_true(model.eval(var))]
        print(f"vertices={len(vertices)} edges={len(chosen)}")
        for u, v in chosen:
            print(f"  {u} -- {v}")


if __name__ == "__main__":
    main()
