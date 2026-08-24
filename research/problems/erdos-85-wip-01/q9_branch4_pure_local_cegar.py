#!/usr/bin/env python3
"""Incremental counterexample search against the reverse-interval target.

The default refinement is the exact negation of Lean's
``HasLocalGramPackingOneRowCompatibilityObstruction`` at an audited bad row:
one target packing together with reverse local packings realizing every one
of its membership bits.  The older pairwise (13ay) refinement remains
available with ``--legacy-pairwise`` for regression comparison.  Thus SAT
with no audited reverse-interval obstruction is a counterexample to the
outer selector, UNSAT rules out every counterexample satisfying the
accumulated exact row witnesses, and UNKNOWN is explicitly inconclusive.
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
    local_packing_family,
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


def all_horns(payload: dict) -> dict:
    system = fixed_system(payload)
    local = {
        u: forced_local_packing_neighbors(system, u) for u in range(N)
    }
    deficit = [u for u in range(N) if not local[u]["packing_count"]]
    reciprocity = []
    for u in range(N):
        for w in local[u]["forced_neighbors"]:
            if u not in local[w]["possible_neighbors"]:
                reciprocity.append((u, w))
    disjoint = []
    for u in range(N):
        for v in range(u + 1, N):
            if not (system["blocks"][u] & system["blocks"][v]):
                continue
            if disjoint_local_packing_pair(system, u, v) is None:
                disjoint.append((u, v))
    reverse_interval = []
    for target in range(N):
        forced_incoming = {
            source for source in range(N)
            if target in local[source]["forced_neighbors"]
        }
        impossible_incoming = {
            source for source in range(N)
            if local[source]["packing_count"]
            and target not in local[source]["possible_neighbors"]
        }
        if not any(
            forced_incoming.issubset(packing)
            and packing.isdisjoint(impossible_incoming)
            for packing in local_packing_family(system, target)
        ):
            reverse_interval.append(target)
    return {
        "deficit": deficit,
        "reciprocity": reciprocity,
        "disjoint": disjoint,
        "reverse_interval": reverse_interval,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--iterations", type=int, default=20)
    parser.add_argument("--timeout-seconds", type=int, default=120)
    parser.add_argument("--random-seed", type=int, default=0)
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument(
        "--legacy-pairwise", action="store_true",
        help="use the older deficit/disjoint/reciprocity refinements",
    )
    parser.add_argument("--output", type=Path)
    parser.add_argument("--integral-row", type=int, action="append", default=[])
    parser.add_argument(
        "--disjoint-pair", type=int, nargs=2, action="append", default=[]
    )
    parser.add_argument(
        "--reciprocity-pair", type=int, nargs=2, action="append", default=[]
    )
    args = parser.parse_args()
    if args.iterations <= 0 or args.timeout_seconds <= 0 or args.threads <= 0:
        parser.error("iterations, timeout, and threads must be positive")

    integral_rows = list(dict.fromkeys(args.integral_row))
    disjoint_pairs = list(dict.fromkeys(
        tuple(sorted(pair)) for pair in args.disjoint_pair
    ))
    reciprocity_pairs = list(dict.fromkeys(
        tuple(pair) for pair in args.reciprocity_pair
    ))
    reverse_interval_rows = []
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
            reverse_interval_rows, integral_rows, None,
        )
        solver.set(random_seed=args.random_seed + iteration)
        solver.set(threads=args.threads)
        result = solver.check()
        record = {
            "iteration": iteration,
            "solver_result": str(result),
            "disjoint_pairs": [list(pair) for pair in disjoint_pairs],
            "reciprocity_pairs": [list(pair) for pair in reciprocity_pairs],
            "integral_rows": integral_rows.copy(),
            "reverse_interval_rows": reverse_interval_rows.copy(),
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
        horns = all_horns(payload)
        new_integral = [u for u in horns["deficit"] if u not in integral_rows]
        new_disjoint = [
            pair for pair in horns["disjoint"] if pair not in disjoint_pairs
        ]
        new_reciprocity = [
            pair for pair in horns["reciprocity"]
            if pair not in reciprocity_pairs
        ]
        new_reverse_interval = [
            target for target in horns["reverse_interval"]
            if target not in reverse_interval_rows
        ][:1] if not new_integral else []
        record["horns"] = {
            "deficit": horns["deficit"],
            "disjoint": [list(pair) for pair in horns["disjoint"]],
            "reciprocity": [list(pair) for pair in horns["reciprocity"]],
            "reverse_interval": horns["reverse_interval"],
        }
        print(json.dumps({
            "iteration": iteration,
            "new_integral_rows": new_integral,
            "new_disjoint_pairs": [list(pair) for pair in new_disjoint],
            "new_reciprocity_pairs": [list(pair) for pair in new_reciprocity],
            "new_reverse_interval_rows": new_reverse_interval,
        }, separators=(",", ":")), flush=True)
        selected_horns = (
            horns["deficit"] or horns["disjoint"] or horns["reciprocity"]
            if args.legacy_pairwise else horns["reverse_interval"]
        )
        if not selected_horns:
            print("pure_local_cegar=counterexample")
            if args.output:
                args.output.write_text(json.dumps(payload, separators=(",", ":")))
            break
        new_selected = (
            new_integral or new_disjoint or new_reciprocity
            if args.legacy_pairwise else
            (new_integral or new_reverse_interval)
        )
        if not new_selected:
            raise RuntimeError("audited horns produced no new refinement")
        if args.legacy_pairwise:
            integral_rows.extend(new_integral)
            disjoint_pairs.extend(new_disjoint)
            reciprocity_pairs.extend(new_reciprocity)
        else:
            integral_rows.extend(new_integral)
            reverse_interval_rows.extend(new_reverse_interval)
    else:
        print("pure_local_cegar=iteration_limit")
    if args.output:
        args.output.with_suffix(args.output.suffix + ".trace.json").write_text(
            json.dumps(trace, indent=2) + "\n"
        )


if __name__ == "__main__":
    main()
