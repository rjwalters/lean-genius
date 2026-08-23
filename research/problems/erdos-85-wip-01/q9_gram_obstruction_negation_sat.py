#!/usr/bin/env python3
"""Seed-free exact negation probe for the B.3 local Gram obstruction (13f).

The unrestricted symbolic outer Q,K design comes from
``q9_b0_residual_defect_sat.build`` with every residual-graph constraint
relaxed.  For each of the 47 indexed B0 blocks this script supplies one
demanded matching in its trace-eligible block hypergraph.  For every ordered
row/candidate pair (t,w), a shared Boolean enables a second demanded matching
at t omitting w.  Whenever two row blocks intersect, the clauses require that
each possible w can be omitted at one endpoint.  This is exactly the formal
negation of ``HasLocalGramPackingObstruction`` banked in
``Erdos85LocalGramPacking.lean``.

SAT refutes candidate (13f).  UNSAT would still require a checked certificate
or a uniform proof; UNKNOWN is only a computational boundary.
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

from z3 import And, Bool, If, Implies, Not, Or, Sum, is_true, sat, unknown

from q9_b0_residual_defect_sat import N, N_TRIPLE, N_U1, build, edge_key


OUTER_ONLY_RELAX = {
    "row-ledger",
    "residual-c4",
    "b0-c4",
    "dtb-common",
    "dtb-cap",
    "dtb-zero",
    "dtb-rows",
    "dtb-columns",
    "marked-miss",
}


def add_negation(branch: int, timeout_ms: int, full: bool = True,
                 symmetric: bool = False):
    solver, data = build(branch, timeout_ms, True, relax=OUTER_ONLY_RELAX)
    incidence = data["incidence"]
    k = data["k"]

    def kadj(a: int, b: int):
        if a == b:
            return False
        return k[edge_key(a, b)]

    holes_begin = N_TRIPLE - (2 if branch == 3 else 4)

    def demand(row: int) -> int:
        return 6 if row >= holes_begin else 5

    # core[t,b] means b lies in the K-neighborhood of block t.  Undirectedness
    # makes this one condition equivalent to both trace exclusions.
    core = {}
    for t in range(N):
        for b in range(N_U1):
            core[t, b] = Bool(f"neg_core_{t}_{b}")
            solver.add(core[t, b] == Or([
                And(incidence[t, a], kadj(a, b))
                for a in range(N_U1) if a != b
            ]))

    eligible = {}
    for t in range(N):
        for u in range(N):
            eligible[t, u] = Bool(f"neg_eligible_{t}_{u}")
            solver.add(eligible[t, u] == And([
                Or(Not(incidence[u, b]), Not(core[t, b]))
                for b in range(N_U1)
            ]))

    def constrain_packing(t: int, chosen: dict[int, object], enabled,
                          omitted: int | None = None,
                          included: int | None = None) -> None:
        solver.add(Implies(enabled,
                           Sum([If(chosen[u], 1, 0) for u in range(N)])
                           == demand(t)))
        for u in range(N):
            if u == t or u == omitted:
                solver.add(Implies(enabled, Not(chosen[u])))
            # If u is chosen at t, its block avoids Gamma_K(B_t).
            solver.add(Implies(And(enabled, chosen[u]), eligible[t, u]))
        if included is not None:
            solver.add(Implies(enabled, chosen[included]))
        # Pairwise block disjointness is exactly one incidence per U1 label.
        for b in range(N_U1):
            solver.add(Implies(
                enabled,
                Sum([If(And(chosen[u], incidence[u, b]), 1, 0)
                     for u in range(N)]) <= 1,
            ))

    base = {}
    for t in range(N):
        chosen = {u: Bool(f"neg_base_{t}_{u}") for u in range(N)}
        base[t] = chosen
        constrain_packing(t, chosen, True)

    if symmetric:
        for t in range(N):
            for u in range(t + 1, N):
                solver.add(base[t][u] == base[u][t])

    avoiding = {}
    containing = {}

    def ensure_avoiding(t: int, w: int):
        if (t, w) not in avoiding:
            enabled = Bool(f"neg_avoid_enabled_{t}_{w}")
            avoiding[t, w] = enabled
            chosen = {u: Bool(f"neg_avoid_{t}_{w}_{u}") for u in range(N)}
            constrain_packing(t, chosen, enabled, omitted=w)
        return avoiding[t, w]

    def ensure_containing(t: int, w: int):
        if (t, w) not in containing:
            enabled = Bool(f"neg_contain_enabled_{t}_{w}")
            containing[t, w] = enabled
            chosen = {u: Bool(f"neg_contain_{t}_{w}_{u}") for u in range(N)}
            constrain_packing(t, chosen, enabled, included=w)
        return containing[t, w]

    added_collision_clauses = set()

    def add_collision_clause(u: int, v: int, w: int) -> None:
        u, v = min(u, v), max(u, v)
        if (u, v, w) in added_collision_clauses:
            return
        added_collision_clauses.add((u, v, w))
        intersects = Or([
            And(incidence[u, b], incidence[v, b]) for b in range(N_U1)
        ])
        solver.add(Or(Not(intersects), ensure_avoiding(u, w),
                      ensure_avoiding(v, w)))

    added_reciprocity_clauses = set()

    def add_reciprocity_clause(u: int, w: int) -> None:
        if (u, w) in added_reciprocity_clauses:
            return
        added_reciprocity_clauses.add((u, w))
        # Negate the horn "u forces w but w can never contain u".
        solver.add(Or(ensure_avoiding(u, w), ensure_containing(w, u)))

    added_one_row_clauses = set()

    def add_one_row_clause(u: int) -> None:
        if u in added_one_row_clauses:
            return
        added_one_row_clauses.add(u)
        # The already-demanded base packing at u must have every membership
        # bit realizable by some packing in the reverse local family.
        for w in range(N):
            solver.add(Or(Not(base[u][w]), ensure_containing(w, u)))
            solver.add(Or(base[u][w], ensure_avoiding(w, u)))

    # Negate every forced collision: if B_u and B_v intersect, then for every
    # w at least one endpoint has a demanded packing omitting w.
    if full:
        for u in range(N):
            for v in range(u + 1, N):
                for w in range(N):
                    add_collision_clause(u, v, w)

    return solver, {
        "incidence": incidence,
        "k": k,
        "demand": demand,
        "add_collision_clause": add_collision_clause,
        "added_collision_clauses": added_collision_clauses,
        "add_reciprocity_clause": add_reciprocity_clause,
        "added_reciprocity_clauses": added_reciprocity_clauses,
        "add_one_row_clause": add_one_row_clause,
        "added_one_row_clauses": added_one_row_clauses,
        "base_variables": N * N,
        "avoid_enabled_variables": len(avoiding),
        "avoid_choice_variables": len(avoiding) * N,
        "core_variables": N * N_U1,
        "eligible_variables": N * N,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=(3, 4), required=True)
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--lazy", action="store_true")
    parser.add_argument("--lazy-reciprocity", action="store_true")
    parser.add_argument("--lazy-one-row", action="store_true")
    parser.add_argument("--symmetric", action="store_true")
    parser.add_argument("--max-rounds", type=int, default=100)
    parser.add_argument("--random-seed", type=int, default=0)
    parser.add_argument("--witness", type=Path)
    args = parser.parse_args()

    build_started = time.time()
    if sum(map(int, (args.lazy, args.lazy_reciprocity, args.lazy_one_row))) > 1:
        parser.error("choose at most one lazy mode")
    solver, counts = add_negation(args.branch, args.timeout_seconds * 1000,
                                  full=not args.lazy and not args.lazy_reciprocity
                                  and not args.lazy_one_row
                                  and not args.symmetric,
                                  symmetric=args.symmetric)
    solver.set(random_seed=args.random_seed)
    if args.witness is not None:
        witness = json.loads(args.witness.read_text())
        fixed_blocks = [set(block) for block in witness["blocks"]]
        fixed_k = {edge_key(*edge) for edge in witness["k_edges"]}
        for u in range(N):
            for b in range(N_U1):
                variable = counts["incidence"][u, b]
                solver.add(variable if b in fixed_blocks[u] else Not(variable))
        for edge, variable in counts["k"].items():
            solver.add(variable if edge in fixed_k else Not(variable))
    build_elapsed = time.time() - build_started
    if args.lazy or args.lazy_reciprocity or args.lazy_one_row:
        from itertools import combinations

        from q9_structured_skew_potential import residual_gram_forced_collisions

        cut_key = ("added_one_row_clauses" if args.lazy_one_row else
                   "added_reciprocity_clauses" if args.lazy_reciprocity else
                   "added_collision_clauses")

        solve_started = time.time()
        for round_number in range(args.max_rounds):
            result = solver.check()
            if result != sat:
                solve_elapsed = time.time() - solve_started
                print(f"branch={args.branch} lazy=True result={result} "
                      f"rounds={round_number + 1} build_seconds={build_elapsed:.3f} "
                      f"solve_seconds={solve_elapsed:.3f} "
                      f"cuts={len(counts[cut_key])}")
                if result == unknown:
                    print(f"reason_unknown={solver.reason_unknown()}")
                    return 2
                candidate = ("one_row_trichotomy" if args.lazy_one_row else
                             "13t" if args.lazy_reciprocity else "13f")
                print(f"candidate_{candidate}_negation=UNSAT_UNCERTIFIED")
                return 0
            model = solver.model()
            blocks = [
                {b for b in range(N_U1)
                 if is_true(model.eval(counts["incidence"][t, b],
                                       model_completion=True))}
                for t in range(N)
            ]
            k_neighbors = [set() for _ in range(N_U1)]
            for (a, b), variable in counts["k"].items():
                if is_true(model.eval(variable, model_completion=True)):
                    k_neighbors[a].add(b)
                    k_neighbors[b].add(a)
            cores = [set().union(*(k_neighbors[b] for b in block))
                     for block in blocks]
            candidates = [[u for u in range(N)
                           if u != t and not (blocks[u] & cores[t])]
                          for t in range(N)]
            concrete = {
                "blocks": blocks,
                "candidates": candidates,
                "degree": [counts["demand"](t) for t in range(N)],
            }
            if args.lazy_reciprocity or args.lazy_one_row:
                feasible = {}
                for row in range(N):
                    feasible[row] = [set(chosen) for chosen in combinations(
                        candidates[row], concrete["degree"][row])
                        if all(not blocks[u] & blocks[v]
                               for u, v in combinations(chosen, 2))]
                reciprocity_horns = [(u, w) for u in range(N) for w in range(N)
                         if feasible[u]
                         and all(w in packing for packing in feasible[u])
                         and feasible[w]
                         and all(u not in packing for packing in feasible[w])]
                collisions = residual_gram_forced_collisions(concrete)
                new_reciprocity = [horn for horn in reciprocity_horns
                                   if horn not in counts["added_reciprocity_clauses"]]
                new_collisions = [horn for horn in collisions
                                  if horn not in counts["added_collision_clauses"]]
                if args.lazy_one_row:
                    forced = {u: set.intersection(*feasible[u]) for u in range(N)}
                    possible = {u: set.union(*feasible[u]) for u in range(N)}
                    bad_rows = [u for u in range(N) if not any(
                        all((w not in packing or u in possible[w]) and
                            (w in packing or u not in forced[w])
                        for w in range(N)) for packing in feasible[u])]
                    interval_profiles = {
                        u: {
                            "block": sorted(blocks[u]),
                            "forced": sorted(w for w in range(N)
                                             if u in forced[w]),
                            "forced_blocks": {
                                w: sorted(blocks[w]) for w in range(N)
                                if u in forced[w]
                            },
                            "impossible": sorted(w for w in range(N)
                                                 if u not in possible[w]),
                            "impossible_candidates": sorted(
                                w for w in candidates[u]
                                if u not in possible[w]),
                            "impossible_candidate_blocks": {
                                w: sorted(blocks[w]) for w in candidates[u]
                                if u not in possible[w]
                            },
                            "packing_count": len(feasible[u]),
                        }
                        for u in bad_rows
                    }
                    for u in bad_rows:
                        required = {w for w in range(N) if u in forced[w]}
                        allowed = [w for w in candidates[u]
                                   if u in possible[w]]
                        # Before old collision cuts are imposed, `required`
                        # need not itself be an allowed prepacking.  Record
                        # that case as -1 rather than crashing the audit.
                        interval_profiles[u]["capacity"] = next((
                            size for size in range(concrete["degree"][u], -1, -1)
                            if any(required <= set(choice) and all(
                                not blocks[x] & blocks[y]
                                for x, y in combinations(choice, 2))
                                for choice in combinations(allowed, size))), -1)
                        if interval_profiles[u]["capacity"] >= 0:
                            forced_labels = set().union(
                                *(blocks[w] for w in required)) if required else set()
                            residual = [w for w in allowed if w not in required
                                        and not blocks[w] & forced_labels]
                            point_cover = next(
                                labels for size in range(N_U1 + 1)
                                for labels in combinations(range(N_U1), size)
                                if all(set(labels) & blocks[w] for w in residual)
                            )
                            interval_profiles[u]["residual_candidates"] = residual
                            interval_profiles[u]["residual_candidate_blocks"] = {
                                w: sorted(blocks[w]) for w in residual
                            }
                            interval_profiles[u]["residual_point_cover"] = list(point_cover)
                            interval_profiles[u]["residual_point_cover_size"] = len(point_cover)
                    new_rows = [u for u in bad_rows
                                if u not in counts["added_one_row_clauses"]]
                    horns = bad_rows + collisions
                    new_obstructions = new_rows + new_collisions
                    label = f"one_row_bad={bad_rows} collisions"
                else:
                    horns = reciprocity_horns + collisions
                    new_obstructions = new_reciprocity + new_collisions
                    label = (f"reciprocity_horns={len(reciprocity_horns)} "
                             f"collisions")
            else:
                horns = residual_gram_forced_collisions(concrete)
                added = counts["added_collision_clauses"]
                new_obstructions = [horn for horn in horns if horn not in added]
                label = "collisions"
            if args.lazy_reciprocity or args.lazy_one_row:
                print(f"lazy_round={round_number + 1} {label}="
                      f"{len(collisions)} new={len(new_obstructions)}")
                if args.lazy_one_row and bad_rows:
                    print("interval_profiles=" + json.dumps(
                        interval_profiles, separators=(",", ":")))
            else:
                print(f"lazy_round={round_number + 1} {label}={len(horns)} "
                      f"new={len(new_obstructions)}")
            if not horns:
                solve_elapsed = time.time() - solve_started
                print(f"branch={args.branch} lazy=True "
                      f"reciprocity={args.lazy_reciprocity} "
                      f"one_row={args.lazy_one_row} result=sat "
                      f"rounds={round_number + 1} build_seconds={build_elapsed:.3f} "
                      f"solve_seconds={solve_elapsed:.3f} "
                      f"cuts={len(counts[cut_key])}")
                if args.lazy_one_row:
                    print("candidate_one_row_trichotomy=REFUTED_IN_OUTER_ABSTRACTION")
                elif args.lazy_reciprocity:
                    print("candidate_13t=REFUTED_IN_OUTER_ABSTRACTION")
                else:
                    print("candidate_13f=REFUTED_IN_OUTER_ABSTRACTION")
                print("counterexample=" + json.dumps({
                    "branch": args.branch,
                    "blocks": [sorted(block) for block in blocks],
                    "k_edges": sorted(
                        [list(edge) for edge, variable in counts["k"].items()
                         if is_true(model.eval(variable, model_completion=True))]
                    ),
                }, separators=(",", ":")))
                return 0
            if not new_obstructions:
                raise RuntimeError("concrete obstruction survived its exact cut")
            for obstruction in new_obstructions:
                if args.lazy_one_row and isinstance(obstruction, int):
                    counts["add_one_row_clause"](obstruction)
                elif args.lazy_reciprocity and obstruction in new_reciprocity:
                    counts["add_reciprocity_clause"](*obstruction)
                else:
                    counts["add_collision_clause"](*obstruction)
        print(f"branch={args.branch} lazy=True result=round-limit "
              f"rounds={args.max_rounds} cuts="
              f"{len(counts[cut_key])}")
        return 2

    solve_started = time.time()
    result = solver.check()
    solve_elapsed = time.time() - solve_started
    print(f"branch={args.branch} symmetric={args.symmetric} result={result} "
          f"build_seconds={build_elapsed:.3f} solve_seconds={solve_elapsed:.3f} "
          f"base_variables={counts['base_variables']} "
          f"core_variables={counts['core_variables']} "
          f"eligible_variables={counts['eligible_variables']}")
    if result == unknown:
        print(f"reason_unknown={solver.reason_unknown()}")
        return 2
    if args.symmetric and result == sat:
        print("symmetric_simultaneous_selection=SAT_IN_OUTER_ABSTRACTION")
    elif args.symmetric:
        print("symmetric_simultaneous_selection=UNSAT_UNCERTIFIED")
    elif result == sat:
        print("candidate_13f=REFUTED_IN_OUTER_ABSTRACTION")
    else:
        print("candidate_13f_negation=UNSAT_UNCERTIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
