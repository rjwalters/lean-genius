#!/usr/bin/env python3
"""Reduced translation-invariant SIZE-TWO-EIGENLINE probe.

An edge from cell ``(x, x+t)`` to ``(x+r, x+r+u)`` is represented by one
Boolean ``E(t,u,r)``.  Reciprocity identifies ``E(t,u,r)`` with
``E(u,t,-r)``.  The model retains the exact row and column hit laws and can
impose selected same-fiber codegree caps without constructing the full
``q(q-2)``-vertex graph.
"""

from __future__ import annotations

import argparse

import z3


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--cap", action="append", default=[],
        help="same-fiber codegree cap DIFFERENCE:SEPARATION")
    parser.add_argument("--empty-fiber", type=int,
        help="forbid every internal edge in this difference fiber")
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    parser.add_argument("--random-seed", type=int, default=0)
    parser.add_argument("--dimacs",
        help="write an equisatisfiable bit-blasted DIMACS instance and exit")
    args = parser.parse_args()

    q = args.q
    holes = {args.a % q, (-1 - args.a) % q}
    differences = [t for t in range(q) if t not in holes]
    variables: dict[tuple[int, int, int], z3.BoolRef] = {}

    def edge_key(t: int, u: int, r: int) -> tuple[int, int, int]:
        forward = (t, u, r % q)
        reverse = (u, t, (-r) % q)
        return min(forward, reverse)

    def edge(t: int, u: int, r: int) -> z3.BoolRef:
        key = edge_key(t, u, r)
        if key not in variables:
            variables[key] = z3.Bool(f"e_{key[0]}_{key[1]}_{key[2]}")
        return variables[key]

    solver = z3.Solver()

    # Looplessness.
    for t in differences:
        solver.add(z3.Not(edge(t, t, 0)))

    # Exact target-row hits.  A route with base displacement r lands in row
    # x+r; rows x+t and x+t+1 are the two holes for source difference t.
    for t in differences:
        for r in range(q):
            wanted = 0 if r in {t, (t + 1) % q} else 1
            solver.add(z3.PbEq([(edge(t, u, r), 1) for u in differences],
                               wanted))

    # Exact target-column hits.  For target column displacement c and target
    # difference u, the target base displacement is r=c-u.
    for t in differences:
        for c in range(q):
            wanted = 0 if c in {0, q - 1} else 1
            solver.add(z3.PbEq([
                (edge(t, u, c - u), 1) for u in differences], wanted))

    for specification in args.cap:
        try:
            raw_t, raw_d = map(int, specification.split(":"))
        except ValueError:
            parser.error("--cap must have form DIFFERENCE:SEPARATION")
        t, d = raw_t % q, raw_d % q
        if t not in differences:
            parser.error(f"cap fiber {t} is forbidden by the two holes")
        # Translation invariance makes the common-neighbor count independent
        # of the source base x.
        solver.add(z3.PbLe([
            (z3.And(edge(t, u, r), edge(t, u, r - d)), 1)
            for u in differences for r in range(q)], 1))

    if args.empty_fiber is not None:
        t = args.empty_fiber % q
        if t not in differences:
            parser.error(f"empty fiber {t} is forbidden by the two holes")
        for r in range(q):
            solver.add(z3.Not(edge(t, t, r)))

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
        print(f"q={q} a={args.a % q} orbit_variables={len(variables)}: "
              f"wrote {args.dimacs}")
        return

    solver.set(timeout=args.timeout_ms, random_seed=args.random_seed)
    result = solver.check()
    print(f"q={q} a={args.a % q} orbit_variables={len(variables)}: {result}")

    if result == z3.sat:
        model = solver.model()
        for t in differences:
            internal_steps = [r for r in range(1, q)
                if z3.is_true(model.eval(edge(t, t, r)))]
            if internal_steps:
                print(f"  fiber {t}: internal_steps={internal_steps}")


if __name__ == "__main__":
    main()
