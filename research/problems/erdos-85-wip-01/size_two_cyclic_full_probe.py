#!/usr/bin/env python3
"""Full base-dependent SIZE-TWO-EIGENLINE feasibility probe.

Unlike ``size_two_cyclic_translation_invariant_probe.py``, this script has
one undirected Boolean edge for every pair of allowed cells.  It directly
encodes exact target-row/column hits, all same-fibre codegree caps, and an
optional empty fibre.
"""

from __future__ import annotations

import argparse
from itertools import combinations

import z3


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--empty-fiber", type=int)
    parser.add_argument("--no-caps", action="store_true")
    parser.add_argument("--directed", action="store_true",
        help="drop reciprocity and use one variable per ordered pair")
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    parser.add_argument("--dimacs")
    args = parser.parse_args()

    q = args.q
    holes = {args.a % q, (-1 - args.a) % q}
    differences = [t for t in range(q) if t not in holes]
    vertices = [(x, t) for x in range(q) for t in differences]
    vertex_set = set(vertices)
    variables: dict[tuple[tuple[int, int], tuple[int, int]], z3.BoolRef] = {}

    def edge(left: tuple[int, int], right: tuple[int, int]) -> z3.BoolRef:
        if left == right:
            return z3.BoolVal(False)
        key = (left, right) if args.directed else tuple(sorted((left, right)))
        if key not in variables:
            (x, t), (y, u) = key
            variables[key] = z3.Bool(f"e_{x}_{t}_{y}_{u}")
        return variables[key]

    solver = z3.Solver()

    # Exact target-row hits: the two neighbours of (x,t) on its own cyclic
    # component would lie in absolute rows x+t and x+t+1, so those rows are
    # holes and every other target row is hit once.
    for source in vertices:
        x, t = source
        for y in range(q):
            wanted = 0 if y in {(x + t) % q, (x + t + 1) % q} else 1
            solver.add(z3.PbEq(
                [(edge(source, (y, u)), 1) for u in differences], wanted))

    # Exact target-column hits.  A cell (y,u) has absolute second coordinate
    # y+u.  Columns x and x-1 are the two component-neighbour holes.
    for source in vertices:
        x, _ = source
        for c in range(q):
            wanted = 0 if c in {x, (x - 1) % q} else 1
            targets = [((c - u) % q, u) for u in differences]
            assert all(target in vertex_set for target in targets)
            solver.add(z3.PbEq(
                [(edge(source, target), 1) for target in targets], wanted))

    # Full same-difference cap: any two distinct bases in one fibre have at
    # most one precise common target cell.
    if not args.no_caps:
        for t in differences:
            for x, z in combinations(range(q), 2):
                left, right = (x, t), (z, t)
                solver.add(z3.PbLe([
                    (z3.And(edge(left, target), edge(right, target)), 1)
                    for target in vertices
                ], 1))

    if args.empty_fiber is not None:
        t = args.empty_fiber % q
        if t not in differences:
            parser.error(f"empty fibre {t} is forbidden by the two holes")
        base_pairs = ((x, z) for x in range(q) for z in range(q) if x != z)
        if not args.directed:
            base_pairs = combinations(range(q), 2)
        for x, z in base_pairs:
            solver.add(z3.Not(edge((x, t), (z, t))))

    if args.dimacs is not None:
        goal = z3.Goal()
        goal.add(*solver.assertions())
        transformed = z3.Then(
            "simplify", "card2bv", "bit-blast", "tseitin-cnf")(goal)
        if len(transformed) != 1:
            raise RuntimeError("CNF conversion unexpectedly produced subgoals")
        cnf_solver = z3.Solver()
        cnf_solver.add(*transformed[0])
        with open(args.dimacs, "w", encoding="ascii") as output:
            output.write(cnf_solver.dimacs())
        print(f"q={q} vertices={len(vertices)} edge_variables={len(variables)}: "
              f"wrote {args.dimacs}")
        return

    solver.set(timeout=args.timeout_ms)
    result = solver.check()
    print(f"q={q} a={args.a % q} vertices={len(vertices)} "
          f"edge_variables={len(variables)}: {result}")


if __name__ == "__main__":
    main()
