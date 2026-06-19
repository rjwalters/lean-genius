# Research State: erdos-1006-oq-01-oq-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-19T11:24:00Z
**Iteration**: 2

## Current Focus
S1 OBSERVE found a definitional soundness bug in the parent Lean file
`Proofs/Erdos1006OQ01.lean`: `hasDependentArc` has its rank inequality
backwards (`rank v ≤ rank u`), so it is vacuously false for every acyclic
orientation, collapsing `isRobustlyAcyclic` to `isAcyclic`. As a result the
target axiom `cover_graph_characterization` is **false** (it asserts every
finite graph is a cover graph; `K₃` refutes it) and lets `False` be derived.
The de-axiomatization is blocked until the definition is repaired.

## Active Approach
Repair-then-prove. (1) Fix `hasDependentArc` to `rank u ≤ rank v` (§3 of S1).
(2) Re-prove `cover_graph_admits_robust` under the corrected def (STEP A).
(3) Prove the reverse direction via the reachability preorder
`Relation.ReflTransGen O.arc` made into a `PartialOrder` (STEP B). (4) Combine
and delete the axiom (STEP C). See S1 note §4 for the full roadmap.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- Build gate: host saturated; `docker-build` clones Mathlib from source (OOM
  risk); cannot compile-verify the §3 fix + STEP A re-proof this session.
- The §3 one-line fix cascades into STEP A (breaks the existing forward proof),
  so it cannot be shipped in isolation without a build.

## Next Action
In a build-capable session: apply §3 fix, re-prove `cover_graph_admits_robust`
(STEP A), formalize the reachability-poset reverse direction (STEP B), build via
`docker-build Proofs.Erdos1006OQ01`, then de-axiomatize (STEP C) and update
`meta.json` axiomCount 3 → 2.
