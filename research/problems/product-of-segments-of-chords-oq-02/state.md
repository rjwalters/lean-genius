# Research State: product-of-segments-of-chords-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15T09:30:00-07:00
**Iteration**: 3

## Current Focus
Lean realization of the integrity finding. Wrote
`proofs/Proofs/ProductOfSegmentsOfChordsConverse.lean` (UNREGISTERED, build-pending):
a machine-checkable **counterexample lemma** proving the unsigned converse axiom is
FALSE, plus the corrected **signed** converse stated in Lean (proof `sorry`,
build-gated circumcenter construction). Prior sessions only had sympy/symbolic certs
(PRs #24105, #24153, #24204) — this is the first Lean encoding of the obstruction.

## Active Approach
Coordinate / circumcenter construction over `EuclideanSpace ℝ (Fin 2)`:
1. Correct the converse statement (signed power `t‖A-P‖² = s‖C-P‖²` +
   linear-independence of `A-P, C-P`).  [DONE — `signed_converse_implies_concyclic`]
2. Build circumcenter of `A,B,C` from the 2×2 perpendicular-bisector system.  [sorry]
3. Show `D` lies on that circle via the signed-power identity; close with `ring`.

## Counterexample (now in Lean)
`unsigned_converse_counterexample_general` (any two unit vectors `e₀, e₁`) and the
concrete `unsigned_converse_counterexample` (standard basis): witness
`P=0, A=e₀, B=-4•e₀, C=e₁, D=4•e₁`. Proof works entirely with squared norms /
polarization (`norm_sub_sq_real`, `real_inner_smul_left`, `norm_smul`): the three
perpendicular-bisector equalities force `⟪e₀,O⟫ = -3/2`, `⟪e₁,O⟫ = 5/2`, and
`⟪e₀,O⟫ = ⟪e₁,O⟫` simultaneously → contradiction. No orthogonality of `e₀,e₁` needed.

## Attempt Count
- Total attempts: 2 (ORIENT paper feasibility; ACT Lean counterexample)
- Current approach attempts: 1 (counterexample lemma written, build-pending)
- Approaches tried: 2

## Blockers
- Docker build + Aristotle MCP unavailable this session (dual blackout) — the Lean
  file is written but NOT machine-checked, and the signed-converse `sorry` (circumcenter
  construction) cannot be discharged/submitted yet. Mathematics fully resolved.

## Next Action
When Docker is available:
1. Build `ProductOfSegmentsOfChordsConverse.lean`; fix any lemma-name drift
   (`EuclideanSpace.norm_single`, `norm_sub_sq_real` are the risk points).
2. Discharge `signed_converse_implies_concyclic` via the circumcenter construction
   (~150-250 LOC) OR submit that single `sorry` to Aristotle.
3. Once both compile, fold the counterexample + corrected statement into the parent
   `ProductOfSegmentsOfChords.lean`, delete the false axiom, drive `axiomCount` → 0,
   register the file in `Proofs.lean`.
