#!/usr/bin/env python3
"""Jointly solve the owner skeleton and symmetric fractional completion."""

from __future__ import annotations

import argparse

import z3

from probe_order49_three_open_code_holonomy import (
    CODES, PAIR01, PAIR02, PAIR12, build_solver, degree, support,
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=("000", "001"), required=True)
    parser.add_argument("--codes", default="0,1")
    parser.add_argument("--timeout-ms", type=int, default=60_000)
    args = parser.parse_args()
    selected = {int(value) for value in args.codes.split(",")}
    if len(selected) != 2 or not selected <= {0, 1, 2}:
        parser.error("--codes must name two distinct colors from 0,1,2")

    solver, owner = build_solver()
    solver.set(timeout=args.timeout_ms)
    matching_edges = (
        owner[0][PAIR01] == PAIR02,
        owner[1][PAIR01] == PAIR12,
        owner[2][PAIR02] == PAIR12,
    )
    if args.profile == "000":
        solver.add(*(z3.Not(edge) for edge in matching_edges))
    else:
        solver.add(z3.Not(matching_edges[0]), matching_edges[1], z3.Not(matching_edges[2]))

    zeros = [v for v in range(46) if support(v) == 0]
    positives = [v for v in range(46) if support(v) > 0]
    x = {
        (v, w): z3.Real(f"x_{v}_{w}")
        for index, v in enumerate(zeros) for w in zeros[index + 1:]
    }
    solver.add(*(value >= 0 for value in x.values()))

    def zero_edge(v: int, w: int) -> z3.ArithRef:
        if v == w:
            return z3.RealVal(0)
        return x[min(v, w), max(v, w)]

    def fixed_edge(zero: int, positive: int) -> z3.BoolRef:
        return z3.Or(*(
            owner[h][zero] == positive
            for h, code in enumerate(CODES) if positive in code
        ))

    for z in zeros:
        fixed_degree = z3.Sum(*(
            z3.If(fixed_edge(z, u), 1, 0) for u in positives
        ))
        solver.add(
            z3.Sum(*(zero_edge(z, w) for w in zeros if w != z))
            + fixed_degree == degree(z)
        )

    for h in selected:
        for u in CODES[h]:
            if support(u) != 1:
                continue
            for z in zeros:
                variable_common = z3.Sum(*(
                    z3.If(owner[h][w] == u, zero_edge(z, w), 0)
                    for w in zeros if w != z
                ))
                fixed_common = z3.Sum(*(
                    z3.If(
                        z3.And(owner[h][w] == u, fixed_edge(z, w)), 1, 0
                    )
                    for w in positives
                ))
                solver.add(variable_common + fixed_common <= 1)

    result = solver.check()
    print(
        f"profile={args.profile} codes={sorted(selected)} "
        f"timeout_ms={args.timeout_ms} result={result}"
    )
    if result == z3.unknown:
        print(f"reason_unknown={solver.reason_unknown()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
