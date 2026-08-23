#!/usr/bin/env python3
"""Independently verify the concrete outer-abstraction counterexample to (13f)."""

from __future__ import annotations

import json
from pathlib import Path

from z3 import Not, is_true, sat

from q9_b0_residual_defect_sat import N, N_U1, build, edge_key
from q9_gram_obstruction_negation_sat import OUTER_ONLY_RELAX
from q9_structured_skew_potential import (
    residual_gram_forced_collisions,
    residual_gram_local_capacities,
)


def main() -> int:
    witness_path = Path(__file__).with_name("q9_13f_counterexample.json")
    witness = json.loads(witness_path.read_text())
    branch = witness["branch"]
    blocks = [set(block) for block in witness["blocks"]]
    k_edges = {edge_key(*edge) for edge in witness["k_edges"]}
    assert len(blocks) == N
    assert all(len(block) == (3 if row < 26 else 2)
               for row, block in enumerate(blocks))

    # Rebuild the unrestricted symbolic outer problem, pin every incidence and
    # K edge to the saved witness, and let Z3 recheck all surviving equations.
    solver, symbolic = build(branch, 60_000, True, relax=OUTER_ONLY_RELAX)
    for row in range(N):
        for label in range(N_U1):
            variable = symbolic["incidence"][row, label]
            solver.add(variable if label in blocks[row] else Not(variable))
    for edge, variable in symbolic["k"].items():
        solver.add(variable if edge in k_edges else Not(variable))
    result = solver.check()
    assert result == sat, f"pinned outer witness failed: {result}"
    model = solver.model()
    assert all(is_true(model.eval(symbolic["incidence"][row, label],
                                  model_completion=True)) == (label in blocks[row])
               for row in range(N) for label in range(N_U1))

    k_neighbors = [set() for _ in range(N_U1)]
    for a, b in k_edges:
        k_neighbors[a].add(b)
        k_neighbors[b].add(a)
    cores = [set().union(*(k_neighbors[label] for label in block))
             for block in blocks]
    candidates = [[u for u in range(N)
                   if u != row and not blocks[u] & cores[row]]
                  for row in range(N)]
    concrete = {
        "blocks": blocks,
        "candidates": candidates,
        "degree": [5 if row < 24 else 6 for row in range(N)],
    }
    deficits = residual_gram_local_capacities(concrete)
    collisions = residual_gram_forced_collisions(concrete)
    assert deficits == [], deficits
    assert collisions == [], collisions
    print("outer_constraints=SAT local_deficits=0 forced_collisions=0")
    print("candidate_13f=REFUTED_IN_OUTER_ABSTRACTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
