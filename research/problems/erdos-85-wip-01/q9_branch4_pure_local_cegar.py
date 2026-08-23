#!/usr/bin/env python3
"""Incremental counterexample search against the pure-local target (13ay).

Every refinement added here is necessary for any genuine counterexample:
an obstructed conflicting pair is required to admit disjoint full packings,
or a forced-forward/impossible-reverse ordered pair is required to admit an
avoiding/containing witness.  Thus SAT with no audited horn is a
counterexample, UNSAT proves the accumulated necessary conditions impossible,
and UNKNOWN is explicitly inconclusive.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from z3 import is_true, sat, unsat

from q9_b0_residual_defect_sat import N, N_U1
from q9_branch4_row_feasible_outer import build_row_feasible
from q9_symmetric_point_mass_obstruction import (
    disjoint_local_packing_pair,
    fixed_system,
    forced_local_packing_neighbors,
)


def payload_from_model(data: dict, model) -> dict:
    return {
        "branch": 4,
        "blocks": [
            [p for p in range(N_U1)
             if is_true(model.eval(data["incidence"][u, p],
                                   model_completion=True))]
            for u in range(N)
        ],
        "k_edges": [
            list(edge) for edge, variable in data["k"].items()
            if is_true(model.eval(variable, model_completion=True))
        ],
    }


def first_horn(payload: dict):
    system = fixed_system(payload)
    local = {
        u: forced_local_packing_neighbors(system, u) for u in range(N)
    }
    deficit = [u for u in range(N) if not local[u]["packing_count"]]
    if deficit:
        return "deficit", deficit[0]
    for u in range(N):
        for v in range(u + 1, N):
            if not (system["blocks"][u] & system["blocks"][v]):
                continue
            if disjoint_local_packing_pair(system, u, v) is None:
                return "disjoint", (u, v)
    for u in range(N):
        for w in local[u]["forced_neighbors"]:
            if u not in local[w]["possible_neighbors"]:
                return "reciprocity", (u, w)
    return None, None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--iterations", type=int, default=20)
    parser.add_argument("--timeout-seconds", type=int, default=120)
    parser.add_argument("--random-seed", type=int, default=0)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--integral-row", type=int, action="append", default=[])
    parser.add_argument(
        "--disjoint-pair", type=int, nargs=2, action="append", default=[]
    )
    parser.add_argument(
        "--reciprocity-pair", type=int, nargs=2, action="append", default=[]
    )
    args = parser.parse_args()
    if args.iterations <= 0 or args.timeout_seconds <= 0:
        parser.error("iterations and timeout must be positive")

    integral_rows = list(dict.fromkeys(args.integral_row))
    disjoint_pairs = list(dict.fromkeys(
        tuple(sorted(pair)) for pair in args.disjoint_pair
    ))
    reciprocity_pairs = list(dict.fromkeys(
        tuple(pair) for pair in args.reciprocity_pair
    ))
    if any(u < 0 or u >= N for u in integral_rows):
        parser.error("--integral-row entries must lie in 0..46")
    if any(u < 0 or u >= N or v < 0 or v >= N or u == v
           for u, v in disjoint_pairs + reciprocity_pairs):
        parser.error("pair entries require distinct rows in 0..46")
    trace = []
    for iteration in range(args.iterations):
        solver, data = build_row_feasible(
            args.timeout_seconds, 12, [], False, False,
            False, False, disjoint_pairs, False, reciprocity_pairs,
            integral_rows, None,
        )
        solver.set(random_seed=args.random_seed + iteration)
        result = solver.check()
        record = {
            "iteration": iteration,
            "solver_result": str(result),
            "disjoint_pairs": [list(pair) for pair in disjoint_pairs],
            "reciprocity_pairs": [list(pair) for pair in reciprocity_pairs],
            "integral_rows": integral_rows.copy(),
        }
        trace.append(record)
        print(json.dumps(record, separators=(",", ":")), flush=True)
        if result == unsat:
            print("pure_local_cegar=unsat")
            break
        if result != sat:
            print("pure_local_cegar=unknown")
            break
        payload = payload_from_model(data, solver.model())
        kind, witness = first_horn(payload)
        record["horn"] = kind
        record["witness"] = witness
        print(json.dumps({
            "iteration": iteration,
            "refinement": kind,
            "witness": witness,
        }, separators=(",", ":")), flush=True)
        if kind is None:
            print("pure_local_cegar=counterexample")
            if args.output:
                args.output.write_text(json.dumps(payload, separators=(",", ":")))
            break
        if kind == "deficit":
            integral_rows.append(witness)
            continue
        if kind == "disjoint":
            disjoint_pairs.append(witness)
        else:
            reciprocity_pairs.append(witness)
    else:
        print("pure_local_cegar=iteration_limit")
    if args.output:
        args.output.with_suffix(args.output.suffix + ".trace.json").write_text(
            json.dumps(trace, indent=2) + "\n"
        )


if __name__ == "__main__":
    main()
