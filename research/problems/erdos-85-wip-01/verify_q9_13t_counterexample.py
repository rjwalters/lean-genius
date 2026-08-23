#!/usr/bin/env python3
"""Verify the durable counterexample to the proposed trichotomy (13t)."""
from __future__ import annotations
import json
from itertools import combinations
from pathlib import Path
from z3 import Bool, If, Not, Solver, Sum, sat
from q9_b0_residual_defect_sat import N, N_U1, build, edge_key
from q9_gram_obstruction_negation_sat import OUTER_ONLY_RELAX
from q9_structured_skew_potential import (
    residual_gram_forced_collisions,
    residual_gram_local_capacities,
    residual_gram_unsat_core,
)

def main() -> int:
    witness = json.loads(Path(__file__).with_name("q9_13t_counterexample.json").read_text())
    blocks = [set(x) for x in witness["blocks"]]
    k_edges = {edge_key(*x) for x in witness["k_edges"]}
    outer, symbolic = build(3, 60_000, True, relax=OUTER_ONLY_RELAX)
    for u in range(N):
        for b in range(N_U1):
            v = symbolic["incidence"][u, b]
            outer.add(v if b in blocks[u] else Not(v))
    for edge, v in symbolic["k"].items():
        outer.add(v if edge in k_edges else Not(v))
    assert outer.check() == sat
    kn = [set() for _ in range(N_U1)]
    for a, b in k_edges: kn[a].add(b); kn[b].add(a)
    cores = [set().union(*(kn[b] for b in block)) for block in blocks]
    candidates = [[v for v in range(N) if v != u and not blocks[v] & cores[u]] for u in range(N)]
    degree = [5 if u < 24 else 6 for u in range(N)]
    data = {"blocks": blocks, "candidates": candidates, "degree": degree,
            "core": cores}
    assert residual_gram_local_capacities(data) == []
    assert residual_gram_forced_collisions(data) == []
    packs = {u: [set(c) for c in combinations(candidates[u], degree[u])
                 if all(not blocks[x] & blocks[y] for x, y in combinations(c, 2))]
             for u in range(N)}
    horns = [(u, w) for u in range(N) for w in range(N)
             if all(w in p for p in packs[u]) and all(u not in p for p in packs[w])]
    assert horns == [], horns
    forced = {u: set.intersection(*packs[u]) for u in range(N)}
    possible = {u: set.union(*packs[u]) for u in range(N)}
    compatible = {
        u: [p for p in packs[u]
            if all((w not in p or u in possible[w])
                   and (w in p or u not in forced[w]) for w in range(N))]
        for u in range(N)
    }
    bad_one_rows = [u for u in range(N) if not compatible[u]]
    solver = Solver(); x = {(u,v): Bool(f"x_{u}_{v}") for u in range(N) for v in range(N)}
    for u in range(N):
        solver.add(Sum([If(x[u,v],1,0) for v in range(N)]) == degree[u])
        for v in range(N):
            if v not in candidates[u]: solver.add(Not(x[u,v]))
        for b in range(N_U1):
            solver.add(Sum([If(x[u,v],1,0) for v in range(N) if b in blocks[v]]) <= 1)
    for u in range(N):
        for v in range(u+1,N): solver.add(x[u,v] == x[v,u])
    result = solver.check()
    core = residual_gram_unsat_core(data, 120)
    assert core["result"] == "unsat", core
    print("outer_constraints=SAT local_deficits=0 forced_collisions=0 reciprocity_horns=0")
    print(f"symmetric_simultaneous_selection={result}")
    print(f"one_row_compatibility_obstructions={bad_one_rows}")
    print("unsat_core=" + json.dumps({
        "degrees": core["degrees"], "gram_pairs": core["gram_pairs"]
    }, separators=(",", ":")))
    print("candidate_13t_trichotomy=REFUTED_IN_OUTER_ABSTRACTION")
    return 0
if __name__ == "__main__": raise SystemExit(main())
