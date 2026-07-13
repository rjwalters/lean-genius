# Research State: konigsberg-oq-03-oq-01

## Current State
**Phase**: ACT (verified instances delivered)
**Path**: fast
**Since**: 2026-06-25
**Iteration**: 2

## Current Focus
Verified the EGW theorem's content (hypotheses + conclusion) for the two
canonical locally finite graphs. General theorem left open (not axiomatized).

## Active Approach
Explicit-witness instances: rayGraphN (ℕ, one-way Euler path) and lineGraphZ
(ℤ, bi-infinite Euler walk). Degree analysis via Set.ncard; covering + edge
injectivity discharged by omega on the identity walk vertex n = n.

## Result
proofs/Proofs/KonigsbergOQ03OQ01.lean — 11 theorems, 19 defs, 0 axioms, 0 sorries.
Key results: IsEulerWalk.existsUnique_step, rayGraphN_hasEulerPath,
rayGraphN_degree_parity, lineGraphZ_hasEulerWalk, lineGraphZ_degree_even.
Axioms: only propext / Classical.choice / Quot.sound (no sorryAx, no ofReduceBool).

## Blockers
General theorem needs König/compactness over a finite exhaustion — not attempted.

## Next Action
Open PR with verified canonical instances. General theorem remains open.
