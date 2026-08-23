#!/usr/bin/env python3
"""Seed-free negation probe for the q=9 full hole-fiber obstruction.

For every point occurrence in an exceptional hole block, this adds a
separate symmetric fractional edge mass satisfying exact degrees on all five
B0 blocks through that point, mutual trace eligibility, and every ordered
point capacity.  By LP duality, such a mass exists exactly when that full
fiber has no strict unit-row-price point-cover certificate with unrestricted
ordered point prices.  This is the global-price relaxation; UNSAT need not
produce the more restrictive local-plus-common-point price mask.

Thus SAT is a concrete outer counterexample to the proposed hole-incidence
selector.  UNSAT would be strong evidence but still needs a checked finite
certificate or a uniform proof.
"""

from __future__ import annotations

import argparse
import json
import time
from itertools import combinations
from pathlib import Path

from z3 import And, If, Implies, Not, Or, Real, Solver, Sum, sat, unknown

from q9_b0_residual_defect_sat import (
    N, N_TRIPLE, N_U1, build, color, edge_key,
)


OUTER_ONLY_RELAX = {
    "row-ledger", "residual-c4", "b0-c4", "dtb-common", "dtb-cap",
    "dtb-zero", "dtb-rows", "dtb-columns", "marked-miss",
}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=(3, 4), required=True)
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--witness", type=Path)
    parser.add_argument(
        "--hole-row", type=int, action="append",
        help="restrict to these exceptional hole rows (repeatable)",
    )
    args = parser.parse_args()

    outer_seed = (
        None if args.witness is None
        else json.loads(args.witness.read_text())
    )
    outer, data = build(
        args.branch, args.timeout_seconds * 1000, True,
        outer_seed=outer_seed, relax=OUTER_ONLY_RELAX,
    )
    solver = Solver()
    solver.set(timeout=args.timeout_seconds * 1000)
    solver.add(*outer.assertions())
    incidence = data["incidence"]
    k = data["k"]

    def kadj(a: int, b: int):
        return False if a == b else k[edge_key(a, b)]

    core = {
        (u, q): Or([
            And(incidence[u, source], kadj(source, q))
            for source in range(N_U1) if source != q
        ])
        for u in range(N) for q in range(N_U1)
    }

    def mutually_eligible(u: int, v: int):
        return And(
            [Implies(incidence[v, q], Not(core[u, q]))
             for q in range(N_U1)]
            + [Implies(incidence[u, q], Not(core[v, q]))
               for q in range(N_U1)]
        )

    mutual = {
        (u, v): mutually_eligible(u, v)
        for u, v in combinations(range(N), 2)
    }

    holes_begin = N_TRIPLE - (2 if args.branch == 3 else 4)
    holes = list(range(holes_begin, N_TRIPLE))
    if args.hole_row is not None:
        if any(row not in holes for row in args.hole_row):
            parser.error(f"--hole-row must lie in {holes}")
        holes = args.hole_row

    def demand(u: int) -> int:
        return 6 if u >= holes_begin else 5

    edge_pairs = list(combinations(range(N), 2))
    systems = 0
    for hole in holes:
        for fiber_color in range(3):
            systems += 1
            mass = {
                pair: Real(
                    f"hf_{hole}_{fiber_color}_{pair[0]}_{pair[1]}"
                )
                for pair in edge_pairs
            }
            for value in mass.values():
                solver.add(value >= 0)

            def edge_mass(u: int, v: int):
                return 0 if u == v else mass[edge_key(u, v)]

            # Capacities do not depend on which point of this color the hole
            # selected, and exactly one is selected, so assert them once.
            for u in range(N):
                for q in range(N_U1):
                    solver.add(Sum([
                        If(incidence[v, q], edge_mass(u, v), 0)
                        for v in range(N) if v != u
                    ]) <= 1)

            for point in range(N_U1):
                if color(point) != fiber_color:
                    continue
                selected = incidence[hole, point]
                # Only edges touching the selected five-root fiber can carry
                # mass, and every positive edge is mutually trace eligible.
                for u, v in edge_pairs:
                    allowed = And(
                        Or(incidence[u, point], incidence[v, point]),
                        mutual[u, v],
                    )
                    solver.add(Implies(
                        And(selected, Not(allowed)), mass[u, v] == 0
                    ))
                # Exact degree is required precisely at the five roots in
                # the selected point fiber.
                for u in range(N):
                    solver.add(Implies(
                        And(selected, incidence[u, point]),
                        Sum([edge_mass(u, v) for v in range(N) if v != u])
                        == demand(u),
                    ))

    print(
        f"branch={args.branch} holes={holes} partial_mass_systems={systems}"
    )
    started = time.monotonic()
    result = solver.check()
    print(f"result={result} elapsed={time.monotonic() - started:.3f}")
    if result == unknown:
        print("reason_unknown=" + solver.reason_unknown())
        return 2
    if result == sat:
        print("hole_fiber_selector_negation=SAT")
        return 0
    print("hole_fiber_selector_negation=UNSAT")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
