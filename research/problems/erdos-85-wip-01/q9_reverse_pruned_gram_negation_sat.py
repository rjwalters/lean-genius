#!/usr/bin/env python3
"""Exact seed-free negation of the reverse-pruned local Gram deficit.

For every row ``u`` the base packing is required to use only candidates
``w`` for which some demanded packing at ``w`` contains ``u``.  Together
with lazy forced-collision cuts, SAT therefore negates the candidate
deficit/collision/reverse-pruned-deficit trichotomy.  UNSAT is only a solver
boundary until converted into a checked certificate or uniform proof.
"""
from __future__ import annotations

import argparse
import json
import time
from itertools import combinations
from pathlib import Path

from z3 import Bool, Implies, Not, is_true, sat, unknown

from q9_b0_residual_defect_sat import N, N_U1, edge_key
from q9_gram_obstruction_negation_sat import add_negation
from q9_structured_skew_potential import residual_gram_forced_collisions


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=(3, 4), default=3)
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--max-rounds", type=int, default=100)
    parser.add_argument("--witness", type=Path)
    args = parser.parse_args()

    started = time.time()
    solver, data = add_negation(
        args.branch, args.timeout_seconds * 1000, full=False, symmetric=False
    )

    # Instantiate reverse witnesses lazily, one obstructed row at a time.
    # Existing reciprocity clauses say Avoiding(u,w) OR Containing(w,u).
    # If the chosen base packing at u contains w, disabling its avoiding
    # witness forces exactly the reverse-containing witness.
    added_pruned_rows: set[int] = set()

    def add_reverse_pruned_row(u: int) -> None:
        if u in added_pruned_rows:
            return
        added_pruned_rows.add(u)
        for w in range(N):
            data["add_reciprocity_clause"](u, w)
            base_uw = Bool(f"neg_base_{u}_{w}")
            avoid_uw = Bool(f"neg_avoid_enabled_{u}_{w}")
            solver.add(Implies(base_uw, Not(avoid_uw)))

    if args.witness is not None:
        witness = json.loads(args.witness.read_text())
        blocks = [set(row) for row in witness["blocks"]]
        k_edges = {edge_key(*edge) for edge in witness["k_edges"]}
        for u in range(N):
            for b in range(N_U1):
                variable = data["incidence"][u, b]
                solver.add(variable if b in blocks[u] else Not(variable))
        for edge, variable in data["k"].items():
            solver.add(variable if edge in k_edges else Not(variable))

    for round_number in range(args.max_rounds):
        result = solver.check()
        if result != sat:
            print(
                f"branch={args.branch} result={result} rounds={round_number + 1} "
                f"seconds={time.time() - started:.3f} "
                f"collision_cuts={len(data['added_collision_clauses'])} "
                f"pruned_rows={len(added_pruned_rows)}"
            )
            if result == unknown:
                print(f"reason_unknown={solver.reason_unknown()}")
                return 2
            print("reverse_pruned_negation=UNSAT_UNCERTIFIED")
            return 0

        model = solver.model()
        blocks = [
            {
                b
                for b in range(N_U1)
                if is_true(
                    model.eval(data["incidence"][u, b], model_completion=True)
                )
            }
            for u in range(N)
        ]
        k_neighbors = [set() for _ in range(N_U1)]
        for (a, b), variable in data["k"].items():
            if is_true(model.eval(variable, model_completion=True)):
                k_neighbors[a].add(b)
                k_neighbors[b].add(a)
        cores = [set().union(*(k_neighbors[b] for b in block)) for block in blocks]
        candidates = [
            [v for v in range(N) if v != u and not blocks[v] & cores[u]]
            for u in range(N)
        ]
        concrete = {
            "blocks": blocks,
            "candidates": candidates,
            "degree": [data["demand"](u) for u in range(N)],
        }
        feasible = {
            u: [
                set(choice)
                for choice in combinations(candidates[u], concrete["degree"][u])
                if all(
                    not blocks[v] & blocks[w]
                    for v, w in combinations(choice, 2)
                )
            ]
            for u in range(N)
        }
        assert all(feasible.values())
        reverse_possible = {
            u: {w for w in range(N) if any(u in packing for packing in feasible[w])}
            for u in range(N)
        }
        reverse_forced = {
            u: {w for w in range(N) if all(u in packing for packing in feasible[w])}
            for u in range(N)
        }
        pruned_bad_rows = [
            u
            for u in range(N)
            if not any(
                packing <= reverse_possible[u] for packing in feasible[u]
            )
        ]
        interval_compatible = {
            u: [
                packing for packing in feasible[u]
                if reverse_forced[u] <= packing <= reverse_possible[u]
            ]
            for u in range(N)
        }
        interval_bad_rows = [u for u in range(N) if not interval_compatible[u]]
        interval_profiles = {
            u: {
                "forced": sorted(reverse_forced[u]),
                "impossible": sorted(set(range(N)) - reverse_possible[u]),
                "packings": len(feasible[u]),
                "compatible": len(interval_compatible[u]),
            }
            for u in interval_bad_rows
        }
        new_pruned_rows = [u for u in pruned_bad_rows if u not in added_pruned_rows]
        collisions = residual_gram_forced_collisions(concrete)
        new_collisions = [
            horn
            for horn in collisions
            if horn not in data["added_collision_clauses"]
        ]
        print(
            f"round={round_number + 1} collisions={len(collisions)} "
            f"new_collisions={len(new_collisions)} "
            f"collision_pairs={collisions} "
            f"pruned_bad_rows={pruned_bad_rows} "
            f"new_pruned_rows={new_pruned_rows} "
            f"interval_bad_rows={interval_bad_rows} "
            f"interval_profiles={interval_profiles}"
        )
        if not collisions and not pruned_bad_rows:
            print("reverse_pruned_trichotomy=REFUTED_IN_OUTER_ABSTRACTION")
            print(
                "counterexample="
                + json.dumps(
                    {
                        "branch": args.branch,
                        "blocks": [sorted(block) for block in blocks],
                        "k_edges": sorted(
                            [
                                list(edge)
                                for edge, variable in data["k"].items()
                                if is_true(
                                    model.eval(variable, model_completion=True)
                                )
                            ]
                        ),
                    },
                    separators=(",", ":"),
                )
            )
            return 0
        if not new_collisions and not new_pruned_rows:
            raise RuntimeError("concrete obstruction survived its exact cut")
        for collision in new_collisions:
            data["add_collision_clause"](*collision)
        for u in new_pruned_rows:
            add_reverse_pruned_row(u)

    print(
        f"branch={args.branch} result=round-limit rounds={args.max_rounds} "
        f"collision_cuts={len(data['added_collision_clauses'])} "
        f"pruned_rows={len(added_pruned_rows)}"
    )
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
