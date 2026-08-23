#!/usr/bin/env python3
"""Fixed-outer residual-relation feasibility probe for q=9 B.3.

This is the inner (Benders) problem suggested by the canonical fractional
interval route.  It pins a stored outer incidence/K payload and solves only
for the residual graph A.  The constraints are necessary for an actual
residual relation: the exact row ledger, mutual trace eligibility, residual
C4-freeness, and zero residual common neighbors for any two B0 blocks which
already share a U1 point.

UNSAT is a rigorous solver result only for the pinned payload, not a uniform
outer-design theorem.  SAT emits the residual edge set for independent
checking or use as the next-stage canonical-interval input.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from itertools import combinations
from pathlib import Path

from z3 import Bool, If, Implies, Not, Or, SolverFor, Sum, is_true, sat

from q9_b0_residual_defect_sat import N, N_TRIPLE, N_U1, build, edge_key


OUTER_ONLY_RELAX = {
    "row-ledger", "residual-c4", "b0-c4", "dtb-common", "dtb-cap",
    "dtb-zero", "dtb-rows", "dtb-columns", "marked-miss",
}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=(3, 4), required=True)
    parser.add_argument("--witness", type=Path)
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--random-seed", type=int, default=0)
    parser.add_argument(
        "--write-outer", type=Path,
        help="write the pinned/generated outer payload for another inner probe",
    )
    parser.add_argument(
        "--relax-inner", action="append", default=[],
        choices=("eligibility", "residual-c4", "block-orthogonal"),
        help="omit one inner residual-relation constraint family",
    )
    parser.add_argument(
        "--eligibility-core", action="store_true",
        help="track forbidden trace edges and emit an UNSAT assumption core",
    )
    parser.add_argument(
        "--degree-core", action="store_true",
        help="track row-degree equations and emit an UNSAT row core",
    )
    parser.add_argument(
        "--minimize-degree-core", action="store_true",
        help="greedily shrink the tracked UNSAT row-degree core",
    )
    args = parser.parse_args()
    if args.minimize_degree_core:
        args.degree_core = True

    if args.witness is None:
        outer, data = build(
            args.branch, args.timeout_seconds * 1000, True,
            relax=OUTER_ONLY_RELAX,
        )
        outer.set(random_seed=args.random_seed)
        outer_result = outer.check()
        print(f"outer_result={outer_result}")
        if outer_result != sat:
            if str(outer_result) == "unknown":
                print("outer_reason_unknown=" + outer.reason_unknown())
                return 2
            return 0
        outer_model = outer.model()
        witness = {
            "branch": args.branch,
            "blocks": [
                [b for b in range(N_U1)
                 if is_true(outer_model.eval(
                     data["incidence"][u, b], model_completion=True))]
                for u in range(N)
            ],
            "k_edges": [
                list(pair) for pair, variable in data["k"].items()
                if is_true(outer_model.eval(variable, model_completion=True))
            ],
        }
    else:
        witness = json.loads(args.witness.read_text())
        witness.setdefault("branch", args.branch)
    if args.write_outer is not None:
        args.write_outer.write_text(json.dumps(witness, indent=2) + "\n")
    fingerprint = hashlib.sha256(json.dumps(
        witness, sort_keys=True, separators=(",", ":")).encode()).hexdigest()[:16]
    print(f"outer_fingerprint={fingerprint}")
    blocks = [set(block) for block in witness["blocks"]]
    if len(blocks) != N:
        raise ValueError(f"expected {N} blocks, got {len(blocks)}")
    k_neighbors = [set() for _ in range(N_U1)]
    for a, b in witness["k_edges"]:
        k_neighbors[a].add(b)
        k_neighbors[b].add(a)
    cores = [set().union(*(k_neighbors[b] for b in block)) for block in blocks]
    eligible = [
        [v != u and not blocks[v] & cores[u] for v in range(N)]
        for u in range(N)
    ]

    holes_begin = N_TRIPLE - (2 if args.branch == 3 else 4)

    def demand(u: int) -> int:
        return 6 if u >= holes_begin else 5

    solver = SolverFor("QF_FD")
    solver.set(timeout=args.timeout_seconds * 1000)
    edge = {edge_key(u, v): Bool(f"a_{u}_{v}")
            for u, v in combinations(range(N), 2)}

    def adj(u: int, v: int):
        return False if u == v else edge[edge_key(u, v)]

    inner_relax = set(args.relax_inner)
    eligibility_assumptions = []
    assumption_edge = {}

    degree_assumptions = []
    assumption_row = {}
    for u in range(N):
        degree_eq = (Sum([If(adj(u, v), 1, 0)
                          for v in range(N) if v != u]) == demand(u))
        if args.degree_core:
            gate = Bool(f"require_degree_{u}")
            degree_assumptions.append(gate)
            assumption_row[gate.decl().name()] = u
            solver.add(Implies(gate, degree_eq))
        else:
            solver.add(degree_eq)
    for u, v in combinations(range(N), 2):
        if ("eligibility" not in inner_relax and
                (not eligible[u][v] or not eligible[v][u])):
            if args.eligibility_core:
                gate = Bool(f"allow_forbid_{u}_{v}")
                eligibility_assumptions.append(gate)
                assumption_edge[gate.decl().name()] = (u, v)
                solver.add(Implies(gate, Not(adj(u, v))))
            else:
                solver.add(Not(adj(u, v)))
        common = [If(adj(u, w) & adj(v, w), 1, 0)
                  for w in range(N) if w not in (u, v)]
        if "residual-c4" not in inner_relax:
            solver.add(Sum(common) <= 1)
        if ("block-orthogonal" not in inner_relax and
                blocks[u] & blocks[v]):
            solver.add(Sum(common) == 0)

    result = solver.check(*(eligibility_assumptions + degree_assumptions))
    print(f"branch={args.branch} result={result}")
    if args.eligibility_core:
        print(f"eligibility_forbidden_count={len(eligibility_assumptions)}")
    if result != sat:
        if str(result) == "unknown":
            print("reason_unknown=" + solver.reason_unknown())
            return 2
        if args.eligibility_core:
            core = [assumption_edge[item.decl().name()]
                    for item in solver.unsat_core()
                    if item.decl().name() in assumption_edge]
            print(f"eligibility_core_size={len(core)}")
            print("eligibility_core=" + json.dumps(
                [list(pair) for pair in sorted(core)], separators=(",", ":")))
            frequency = [sum(v in pair for pair in core) for v in range(N)]
            print("eligibility_core_vertex_frequency=" + json.dumps(
                frequency, separators=(",", ":")))
        if args.degree_core:
            degree_gate = {gate.decl().name(): gate
                           for gate in degree_assumptions}
            current = [degree_gate[item.decl().name()]
                       for item in solver.unsat_core()
                       if item.decl().name() in degree_gate]
            if args.minimize_degree_core:
                changed = True
                while changed:
                    changed = False
                    for gate in list(current):
                        trial = [item for item in current if not item.eq(gate)]
                        trial_result = solver.check(
                            *(eligibility_assumptions + trial))
                        if str(trial_result) == "unsat":
                            trial_names = {
                                item.decl().name()
                                for item in solver.unsat_core()
                                if item.decl().name() in degree_gate
                            }
                            current = [item for item in trial
                                       if item.decl().name() in trial_names]
                            changed = True
                            break
            degree_core = [assumption_row[item.decl().name()]
                           for item in current]
            print(f"degree_core_size={len(degree_core)}")
            print("degree_core=" + json.dumps(sorted(degree_core),
                                               separators=(",", ":")))
            profiles = {
                str(u): {
                    "block": sorted(blocks[u]),
                    "demand": demand(u),
                    "mutually_eligible": [
                        v for v in range(N)
                        if v != u and eligible[u][v] and eligible[v][u]
                    ],
                }
                for u in sorted(degree_core)
            }
            core_intersections = [
                [u, v, sorted(blocks[u] & blocks[v])]
                for u, v in combinations(sorted(degree_core), 2)
                if blocks[u] & blocks[v]
            ]
            print("degree_core_profiles=" + json.dumps(
                profiles, separators=(",", ":")))
            print("degree_core_intersections=" + json.dumps(
                core_intersections, separators=(",", ":")))
        print("fixed_outer_relation_base=UNSAT")
        return 0
    model = solver.model()
    chosen_set = {pair for pair, variable in edge.items()
                  if is_true(model.eval(variable, model_completion=True))}
    chosen = [list(pair) for pair in sorted(chosen_set)]
    degree = [sum(edge_key(u, v) in chosen_set for v in range(N) if v != u)
              for u in range(N)]
    print("fixed_outer_relation_base=SAT")
    print("degree=" + json.dumps(degree, separators=(",", ":")))
    print("residual_edges=" + json.dumps(chosen, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
