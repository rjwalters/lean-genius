# Research State: product-of-segments-of-chords-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14T17:42:10-07:00
**Iteration**: 2

## Current Focus
Feasibility resolved on paper. Identified that the target axiom is FALSE as
typed (unsigned products) and produced the corrected, provable formulation plus
a coordinate proof outline. Implementation is build-gated (Docker down).

## Active Approach
Coordinate / circumcenter construction over `EuclideanSpace ℝ (Fin 2)`:
1. Correct the converse statement (signed power `t‖A-P‖² = s‖C-P‖²` +
   linear-independence of `A-P, C-P`).
2. Build circumcenter of `A,B,C` from the 2×2 perpendicular-bisector system.
3. Show `D` lies on that circle via the signed-power identity; close with `ring`.

## Attempt Count
- Total attempts: 1 (paper feasibility / ORIENT)
- Current approach attempts: 0 (no Lean written — Docker unavailable)
- Approaches tried: 1

## Blockers
- Docker build unavailable this session — cannot compile/verify Lean, so the
  proof itself is deferred. The mathematics is fully resolved (no math blocker).

## Next Action
When Docker is available:
1. Edit `proofs/Proofs/ProductOfSegmentsOfChords.lean` to correct the converse
   statement (see knowledge.md "Corrected, provable formulation").
2. Implement the circumcenter construction proof (~150-250 LOC, BUILD decision).
3. Drive `axiomCount` to 0 and add a Lean counterexample lemma guarding the
   unsigned form.
