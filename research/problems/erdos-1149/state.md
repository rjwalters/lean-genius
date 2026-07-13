# Current State

**Phase**: COMPLETED (axiom-elimination subgoal achieved; Bergelson–Richter axiom retained by design)
**Since**: 2026-05-17 (S4 STATE-SYNC; subgoal completed by PR #15578 on an earlier date)
**Iteration**: 4

## Current Focus

No active research focus. The `random_coprime_density` axiom-elimination subgoal that motivated the ACT phase (iter 3) was completed by PR #15578 — `random_coprime_density` is now a proved theorem in `Erdos1149Problem.lean` (line 162), reducing the file's axiom count from 2 to 1.

The remaining `bergelson_richter` axiom is retained by mathematical-design judgment: it encapsulates the deep ergodic-theory main theorem of Bergelson–Richter (2017), which sits well outside Mathlib's current reach (Bergelson–Host–Kra structure theorem, nilfactor analysis, multiplicative-function-along-polynomial-sequences machinery).

## Active Approach

None active. The Möbius+Tannery approach previously documented as the elimination path was successfully executed in PR #15578 (via `BaselProblemOQ04OQ03.coprime_pair_density_limit`).

## Blockers

None. The slug is in a stable rest state: gallery `status: axiomatized`, `badge: axiom`, 1 axiom (`bergelson_richter`) by design.

## Next Action

No queued action. Future re-engagement candidates (low priority, all stretch):

- **A. Bergelson–Richter formalization** — Multi-year effort; would require building Bergelson–Host–Kra and a nilfactor library. Not tractable in current Mathlib.
- **B. Alternative elementary proofs of Bergelson–Richter** — Survey for any post-2017 elementary or simpler proofs that could shrink the formalization gap.
- **C. Strengthen related infrastructure** — The Möbius and density lemmas in `Erdos1149Problem.lean` may be useful for sibling Erdős slugs; consider abstracting reusable pieces.

## Attempt Counts

- Total attempts: 1 (this STATE-SYNC after PR #15578 already eliminated the documented axiom-elimination target)
- Current approach attempts: 0
- Approaches tried: 1 (Möbius+Tannery — succeeded in PR #15578)
