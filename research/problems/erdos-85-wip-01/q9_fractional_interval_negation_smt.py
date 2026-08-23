#!/usr/bin/env python3
"""Seed-free negation probe for the q=9 fractional interval certificate.

For every outer row ``u`` this asks for a fractional matching ``x[u,*]`` of
the demanded size.  Positive mass on candidate ``w`` is backed by an
*integral* demanded packing at reverse row ``w`` which contains ``u``;
mass below one is backed by an integral demanded packing at ``w`` which
avoids ``u``.  Thus the support avoids the canonical reverse-impossible set
and every canonical reverse-forced candidate has coefficient one.

SAT produces a counterexample in the deliberately relaxed outer abstraction;
it refutes the full prospective assertion only if the emitted payload is then
verified against the omitted full-admissibility constraints.  UNSAT is useful
classification evidence but still needs a checked certificate or a uniform
proof; UNKNOWN is only a computational boundary.
"""

from __future__ import annotations

import argparse
import json
from itertools import combinations
from pathlib import Path

from z3 import And, Bool, If, Implies, Not, Or, Real, Solver, Sum, is_true, sat

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


def add_fractional_interval_negation(branch: int, timeout_ms: int,
                                     witness: dict | None = None):
    outer, data = build(branch, timeout_ms, True, relax=OUTER_ONLY_RELAX)
    solver = Solver()
    solver.set(timeout=timeout_ms)
    solver.add(*outer.assertions())
    incidence = data["incidence"]
    k = data["k"]

    if witness is not None:
        fixed_blocks = [set(block) for block in witness["blocks"]]
        fixed_k = {edge_key(*edge) for edge in witness["k_edges"]}
        for u in range(N):
            for b in range(N_U1):
                solver.add(incidence[u, b] == (b in fixed_blocks[u]))
        for edge, variable in k.items():
            solver.add(variable == (edge in fixed_k))

    holes_begin = N_TRIPLE - (2 if branch == 3 else 4)

    def demand(row: int) -> int:
        return 6 if row >= holes_begin else 5

    def kadj(a: int, b: int):
        return False if a == b else k[edge_key(a, b)]

    core = {}
    eligible = {}
    for row in range(N):
        for point in range(N_U1):
            core[row, point] = Bool(f"fi_core_{row}_{point}")
            solver.add(core[row, point] == Or([
                And(incidence[row, other], kadj(other, point))
                for other in range(N_U1) if other != point
            ]))
        for candidate in range(N):
            eligible[row, candidate] = Bool(f"fi_eligible_{row}_{candidate}")
            solver.add(eligible[row, candidate] == And([
                Or(Not(incidence[candidate, point]),
                   Not(core[row, point]))
                for point in range(N_U1)
            ]))

    def constrain_integral_packing(row: int, chosen: dict[int, object],
                                   enabled, included: int | None = None,
                                   omitted: int | None = None) -> None:
        solver.add(Implies(enabled, Sum([
            If(chosen[v], 1, 0) for v in range(N)
        ]) == demand(row)))
        for v in range(N):
            if v == row or v == omitted:
                solver.add(Implies(enabled, Not(chosen[v])))
            solver.add(Implies(And(enabled, chosen[v]), eligible[row, v]))
        if included is not None:
            solver.add(Implies(enabled, chosen[included]))
        for point in range(N_U1):
            solver.add(Implies(enabled, Sum([
                If(And(chosen[v], incidence[v, point]), 1, 0)
                for v in range(N)
            ]) <= 1))

    # The interval families are meaningful only after local feasibility.  A
    # single demanded packing per row is cheap; reverse containing/avoiding
    # witnesses are introduced lazily below.
    for row in range(N):
        base = {v: Bool(f"fi_base_{row}_{v}") for v in range(N)}
        constrain_integral_packing(row, base, True)

    mass = {(u, w): Real(f"fi_mass_{u}_{w}")
            for u in range(N) for w in range(N)}
    for u in range(N):
        solver.add(Sum([mass[u, w] for w in range(N)]) == demand(u))
        for w in range(N):
            solver.add(mass[u, w] >= 0, mass[u, w] <= 1)
            if u == w:
                solver.add(mass[u, w] == 0)
            solver.add(Implies(mass[u, w] > 0, eligible[u, w]))
        for point in range(N_U1):
            solver.add(Sum([
                If(incidence[w, point], mass[u, w], 0)
                for w in range(N)
            ]) <= 1)

    # With a fixed outer payload, compute the reverse interval exactly in
    # Python.  This is both much smaller and a useful soundness regression for
    # the symbolic witness implications below.
    if witness is not None:
        blocks = [set(block) for block in witness["blocks"]]
        k_neighbors = [set() for _ in range(N_U1)]
        for a, b in witness["k_edges"]:
            k_neighbors[a].add(b)
            k_neighbors[b].add(a)
        cores = [set().union(*(k_neighbors[b] for b in block))
                 for block in blocks]
        candidates = [[v for v in range(N)
                       if v != row and not blocks[v] & cores[row]]
                      for row in range(N)]
        feasible = {}
        for row in range(N):
            feasible[row] = [set(chosen) for chosen in combinations(
                candidates[row], demand(row))
                if all(not blocks[v] & blocks[w]
                       for v, w in combinations(chosen, 2))]
            if not feasible[row]:
                solver.add(False)
        if all(feasible[row] for row in range(N)):
            forced = {row: set.intersection(*feasible[row]) for row in range(N)}
            possible = {row: set.union(*feasible[row]) for row in range(N)}
            for u in range(N):
                for w in range(N):
                    if u in forced[w]:
                        solver.add(mass[u, w] == 1)
                    if u not in possible[w]:
                        solver.add(mass[u, w] == 0)
        return solver, mass, {"fixed": True}

    # Reverse witnesses make the interval conditions exact.  When x[u,w]>0,
    # u is possible at reverse row w; when x[u,w]<1, u is avoidable there.
    added_pairs: set[tuple[int, int]] = set()

    def add_reverse_pair(u: int, w: int) -> None:
        if (u, w) in added_pairs:
            return
        added_pairs.add((u, w))
        containing = {v: Bool(f"fi_contain_{u}_{w}_{v}") for v in range(N)}
        avoiding = {v: Bool(f"fi_avoid_{u}_{w}_{v}") for v in range(N)}
        constrain_integral_packing(
            w, containing, mass[u, w] > 0, included=u)
        constrain_integral_packing(
            w, avoiding, mass[u, w] < 1, omitted=u)

    return solver, mass, {
        "fixed": False,
        "incidence": incidence,
        "k": k,
        "demand": demand,
        "add_reverse_pair": add_reverse_pair,
        "added_pairs": added_pairs,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=(3, 4), required=True)
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--random-seed", type=int, default=0)
    parser.add_argument("--max-rounds", type=int, default=100)
    parser.add_argument("--witness", type=Path)
    args = parser.parse_args()

    witness = json.loads(args.witness.read_text()) if args.witness else None
    solver, mass, data = add_fractional_interval_negation(
        args.branch, args.timeout_seconds * 1000, witness)
    solver.set(random_seed=args.random_seed)
    for round_number in range(1, args.max_rounds + 1):
        result = solver.check()
        print(f"round={round_number} result={result} "
              f"reverse_pairs={len(data.get('added_pairs', ())) }")
        if result != sat:
            if str(result) == "unknown":
                print("reason_unknown=" + solver.reason_unknown())
            return 2
        model = solver.model()
        if data["fixed"]:
            # A fixed known-deficient payload is expected to stop above at
            # UNSAT.  Reaching this branch would be a counterexample payload.
            print(f"branch={args.branch} result=sat fixed_counterexample=true")
        else:
            blocks = [
                {b for b in range(N_U1)
                 if is_true(model.eval(data["incidence"][u, b],
                                       model_completion=True))}
                for u in range(N)
            ]
            k_neighbors = [set() for _ in range(N_U1)]
            for (a, b), variable in data["k"].items():
                if is_true(model.eval(variable, model_completion=True)):
                    k_neighbors[a].add(b)
                    k_neighbors[b].add(a)
            cores = [set().union(*(k_neighbors[b] for b in block))
                     for block in blocks]
            candidates = [[v for v in range(N)
                           if v != row and not blocks[v] & cores[row]]
                          for row in range(N)]
            feasible = {
                row: [set(chosen) for chosen in combinations(
                    candidates[row], data["demand"](row))
                    if all(not blocks[v] & blocks[w]
                           for v, w in combinations(chosen, 2))]
                for row in range(N)
            }
            if any(not feasible[row] for row in range(N)):
                raise RuntimeError("base packing constraint survived without packing")
            forced = {row: set.intersection(*feasible[row]) for row in range(N)}
            possible = {row: set.union(*feasible[row]) for row in range(N)}
            violations = []
            for u in range(N):
                for w in range(N):
                    value = model.eval(mass[u, w]).as_fraction()
                    if ((value > 0 and u not in possible[w]) or
                            (value < 1 and u in forced[w])):
                        violations.append((u, w))
            new_pairs = [pair for pair in violations
                         if pair not in data["added_pairs"]]
            print(f"violations={len(violations)} new_pairs={len(new_pairs)}")
            if violations:
                if not new_pairs:
                    raise RuntimeError("reverse violation survived its exact cut")
                for pair in new_pairs:
                    data["add_reverse_pair"](*pair)
                continue
            print(f"branch={args.branch} result=sat "
                  "fractional_interval_negation="
                  "SAT_IN_RELAXED_OUTER_ABSTRACTION")
        support = {
            str(u): {str(w): str(model.eval(mass[u, w]))
                     for w in range(N)
                     if model.eval(mass[u, w]).as_fraction() > 0}
            for u in range(N)
        }
        print("fractional_interval_support=" +
              json.dumps(support, separators=(",", ":")))
        return 0
    print(f"branch={args.branch} result=round-limit rounds={args.max_rounds} "
          f"reverse_pairs={len(data['added_pairs'])}")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
