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

from z3 import Bool, If, Not, Or, SolverFor, Sum, is_true, sat

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
    args = parser.parse_args()

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

    for u in range(N):
        solver.add(Sum([If(adj(u, v), 1, 0)
                        for v in range(N) if v != u]) == demand(u))
    for u, v in combinations(range(N), 2):
        if not eligible[u][v] or not eligible[v][u]:
            solver.add(Not(adj(u, v)))
        common = [If(adj(u, w) & adj(v, w), 1, 0)
                  for w in range(N) if w not in (u, v)]
        solver.add(Sum(common) <= 1)
        if blocks[u] & blocks[v]:
            solver.add(Sum(common) == 0)

    result = solver.check()
    print(f"branch={args.branch} result={result}")
    if result != sat:
        if str(result) == "unknown":
            print("reason_unknown=" + solver.reason_unknown())
            return 2
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
