# Current State

**Phase**: AXIOMATIZED
**Since**: 2026-01-15T14:38:41.571Z (NEW); 2026-03-26 (initial research, PR #6990); 2026-05-03 (last meta-fix, PR #14994)
**Last Updated**: 2026-05-13 (state-sync per `sessions/2026-05-13-state-sync-axiomatized-multi-file.md`)
**Iteration**: 8

## Current Focus

Stable "axiomatized" steady state. 3-file deliverable:

- `proofs/Proofs/Erdos1065Problem.lean` — main, 1 axiom (`erdos_1065a` line 37; open Erdős conjecture)
- `proofs/Proofs/Erdos1065BatemanHorn.lean` — 1 axiom (Bateman-Horn conjecture infrastructure)
- `proofs/Proofs/Erdos1065CunninghamChains.lean` — 1 axiom (Cunningham chain structural axiom)

**Total: 3 axioms, 0 sorries.**

Per `CLAUDE.md` Axiom Integrity Policy: these are load-bearing assumptions
(open conjecture + Bateman-Horn deep conjecture + Cunningham structural).

## Active Approach

Multi-file decomposition: main problem statement + Bateman-Horn machinery
(restricted to k ≥ 1 per PR #14237) + Cunningham chain infrastructure.
k-layer characterizations (k=0,2,3) and Erdős 1065a bridge added in recent
work.

## Blockers

None — slug is in stable steady state. The 3 axioms are load-bearing.

## Next Action

Slug is stable. Optional future work:

1. **State.md drift sync** (this PR): from NEW/iter 1/2026-01-15 →
   AXIOMATIZED/iter 8/2026-05-03. **Completed in this session.**
2. **JSON drift-sync** (Mechanic territory): sync research JSON top-level
   `phase` / `currentState.phase` from drifted `OBSERVE` / `ACT` to
   `"AXIOMATIZED"`.
3. **Mathlib upstream watch**: if Bateman-Horn proof lands in Mathlib (unlikely
   near-term — it's a major open conjecture itself for general k > 1), the
   Bateman-Horn axiom can be replaced.

## Attempt Counts

- Total attempts: 5+
- Current approach attempts: 1 (axiomatization, stable)
- Approaches tried:
  1. Initial research (PR #6990, 2026-03-26)
  2. Multi-pass enrichment (PR #4297, #5240, #5497, #5869, #9456, 2026-03 to 2026-04)
  3. Restrict BH axiom + k-layer characterizations (PR #14237, 2026-05-01)
  4. Reconcile meta.json with Lean file (PR #14994, 2026-05-03)
