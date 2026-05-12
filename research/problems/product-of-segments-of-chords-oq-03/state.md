# Research State: product-of-segments-of-chords-oq-03

## Current State

**Phase**: OBSERVE
**Path**: full
**Since**: 2026-05-12T18:00:00Z (researcher-11)
**Iteration**: 1

## Current Focus

S1 OBSERVE complete: documented the power-of-a-point ↔ four-point concyclicity
determinant bridge, surveyed Mathlib API, decomposed the goal into S2–S6, and verified
the determinant criterion on a numerical example (unit-circle vertices give $\Delta = 0$;
off-circle gives $\Delta = -8$).

The deliverable closes parent `converse_product_implies_concyclic_axiom` (line 468 of
`Proofs/ProductOfSegmentsOfChords.lean`). After S6, parent `axiomCount` drops 1 → 0.

## Active Approach

Companion file `Proofs/ProductOfSegmentsOfChordsOQ03.lean` defining the $4 \times 4$
concyclicity determinant and proving the bidirectional concyclicity criterion via
Cramer's rule, then using it to discharge the parent axiom.

## Attempt Count

- Total attempts: 1 (S1 OBSERVE)
- Current approach attempts: 1
- Approaches tried: 1 (determinant + Cramer)

## Blockers

None known. The strategy is purely algebraic and does not depend on Mathlib's
`Affine.Simplex.circumcenter` (which would otherwise require bridging
`Vec2 := Fin 2 → ℝ` with `EuclideanSpace ℝ (Fin 2)`).

## Next Action

**S2 (any researcher)**: create `Proofs/ProductOfSegmentsOfChordsOQ03.lean` with:

1. `def concyclicityDet (P₁ P₂ P₃ P₄ : Vec2) : ℝ := Matrix.det !![...]` (~10 lines).
2. Numerical example (`example : concyclicityDet ![1,0] ![0,1] ![-1,0] ![0,-1] = 0`),
   provable by `decide`/`norm_num` (~5 lines).
3. Statement of the main theorem with `by sorry` (1 sorry).

Target: 1 SCAFFOLD PR (~40 lines, build verified on the docker wrapper).

## Subsequent Plan

| Session | Goal | Lines | Sorries |
| --- | --- | --- | --- |
| S2 | Define `concyclicityDet`, state main theorem with sorry. | ~40 | +1 |
| S3 | (⇐) `Δ = 0 ∧ non-collinear → ∃ O r, ...` via Cramer. | ~80 | -0 +0 (close 1, open 1) |
| S4 | (⇒) `concyclic → Δ = 0` via row reduction. | ~30 | -1 |
| S5 | Bridge: `chord_product_equal → Δ = 0`. | ~50 | -1 |
| S6 | Replace axiom; update parent meta. | ~10 | parent ax 1 → 0 |

Total after S6: ~210 lines of new content, parent axiom discharged.

## References

- Parent file: `Proofs/ProductOfSegmentsOfChords.lean`
- Parent gallery: `src/data/proofs/product-of-segments-of-chords/`
- Parent openQuestion #3: `meta.json:conclusion.openQuestions[2]` references this exact
  problem.
- See `problem.md` (this directory) for full formal statement.
- See `knowledge.md` (this directory) for Mathlib API survey and proof strategy.
