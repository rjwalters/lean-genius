#!/usr/bin/env python3
"""Generate branch-4 outer designs on the fractional row-feasible locus.

The ordinary random outer-design sweep is a poor test of the proposed
global-special load selector: almost every generated design already has a
strict one-row point cover.  This script adds the *dual* condition for every
row directly to the outer SMT instance.  For each selected row ``u`` it asks
for a fractional packing on mutually trace-eligible candidate rows ``v`` such that

    sum_v w[u,v] >= d(u),
    sum_{v : p in B_v} w[u,v] <= 1  for every U1 point p.

By fractional LP duality this is exactly the assertion that the selected
row's minimum one-row point-cover cost is at least ``d(u)``.  The fast default
selects the four exceptional rows; the emitted payload is then independently
rechecked on all 47 rows with the rational LP auditor in
``q9_symmetric_point_mass_obstruction.py``; this file is an exploratory
generator, not a proof certificate.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from z3 import And, Bool, If, Implies, Int, Not, Or, Sum, is_true, sat

from q9_b0_residual_defect_sat import N, N_TRIPLE, N_U1, build, edge_key
from q9_symmetric_point_mass_obstruction import (
    OUTER_ONLY_RELAX, fixed_system, unit_row_cover_optimum,
)


def build_row_feasible(timeout_seconds: int, denominator: int,
                       rows: list[int], template: dict | None = None):
    solver, data = build(
        4, timeout_seconds * 1000, True, outer_seed=template,
        relax=OUTER_ONLY_RELAX
    )

    incidence = data["incidence"]
    k = data["k"]

    def kadj(a: int, b: int):
        return False if a == b else k[edge_key(a, b)]

    def core(row: int, point: int):
        return Or([
            And(incidence[row, source], kadj(source, point))
            for source in range(N_U1) if source != point
        ])

    def eligible(u: int, v: int):
        return And([
            Implies(incidence[v, point], Not(core(u, point)))
            for point in range(N_U1)
        ])

    packing = {}
    for u in rows:
        for v in range(N):
            if u == v:
                continue
            # A bounded common denominator keeps the augmented instance in
            # QF_FD.  This is stronger than unrestricted fractional row
            # feasibility, but every SAT model is a valid fractional model.
            weight = (If(Bool(f"row_pack_bool_{u}_{v}"), 1, 0)
                      if denominator == 1 else Int(f"row_pack_{u}_{v}"))
            packing[u, v] = weight
            if denominator != 1:
                solver.add(weight >= 0, weight <= denominator)
            solver.add(Implies(
                Not(And(eligible(u, v), eligible(v, u))), weight == 0
            ))

        degree = 6 if u >= N_TRIPLE - 4 else 5
        solver.add(Sum([packing[u, v] for v in range(N) if v != u]) >=
                   denominator * degree)
        for point in range(N_U1):
            solver.add(Sum([
                If(incidence[v, point], packing[u, v], 0)
                for v in range(N) if v != u
            ]) <= denominator)

    return solver, data


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--random-seed", type=int, default=0)
    parser.add_argument("--denominator", type=int, default=12)
    parser.add_argument(
        "--template", type=Path,
        help="fix the outer design to a payload (encoding regression mode)",
    )
    parser.add_argument(
        "--rows", type=int, nargs="*", default=list(range(22, 26)),
        help=("rows whose fractional feasibility is imposed; defaults to "
              "the four exceptional branch-4 holes 22..25"),
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    if args.denominator <= 0:
        parser.error("--denominator must be positive")
    if any(row < 0 or row >= N for row in args.rows):
        parser.error("--rows entries must lie in 0..46")
    template = json.loads(args.template.read_text()) if args.template else None
    solver, data = build_row_feasible(
        args.timeout_seconds, args.denominator, args.rows, template=template
    )
    solver.set(random_seed=args.random_seed)
    result = solver.check()
    print(f"row_feasible_outer={result}")
    if result != sat:
        return
    model = solver.model()
    payload = {
        "branch": 4,
        "blocks": [
            [point for point in range(N_U1)
             if is_true(model.eval(data["incidence"][row, point],
                                   model_completion=True))]
            for row in range(N)
        ],
        "k_edges": [
            list(edge) for edge, variable in data["k"].items()
            if is_true(model.eval(variable, model_completion=True))
        ],
    }
    system = fixed_system(payload)
    strict_rows = [
        row for row in range(N)
        if unit_row_cover_optimum(system, row)["strict"]
    ]
    print(f"independent_strict_one_row_covers={strict_rows}")
    print(f"all_rows_fractionally_feasible={not strict_rows}")
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(encoded, end="")
    else:
        args.output.write_text(encoded)
        print(f"wrote={args.output}")


if __name__ == "__main__":
    main()
