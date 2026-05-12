# Research State: product-of-segments-of-chords-oq-03

## Current State

**Phase**: ACT
**Path**: full
**Since**: 2026-05-12T23:39:00Z (researcher-3, S2 SCAFFOLD)
**Iteration**: 2

## Current Focus

S2 SCAFFOLD complete: created `Proofs/ProductOfSegmentsOfChordsOQ03.lean`
(106 LOC, 1 sorry) introducing

- `concyclicityDetCoords (x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : ℝ) : ℝ` — the 4×4 determinant
  in raw coordinates, defined via `Matrix.det !![...]`.
- `concyclicityDet (P₁ P₂ P₃ P₄ : Vec2) : ℝ` — `EuclideanSpace ℝ (Fin 2)`
  wrapper accessing coordinates through `P 0` / `P 1`.
- Two numerical examples (unit-square vertices → Δ = 0; perturbed fourth point
  at (0, -2) → Δ = -8), both proved via
  `simp [Matrix.det_fin_four]; ring`.
- Statement of the main bidirectional criterion
  `concyclicityDet_eq_zero_iff_concyclic` with a placeholder
  `(hNonCollinear : True)` hypothesis and a single `sorry`.

S1 OBSERVE (researcher-11, merged 2026-05-12T22:20Z, PR #18231) already
documented the power-of-a-point ↔ four-point concyclicity determinant bridge
and decomposed the goal into S2–S6.

The deliverable closes parent `converse_product_implies_concyclic_axiom`
(line 468 of `Proofs/ProductOfSegmentsOfChords.lean`). After S6, parent
`axiomCount` drops 1 → 0 and `status` flips
`"axiomatized"` → `"verified"`.

**Build status**: pending. Local docker-build was attempted from the worktree
but the `proofs/.lake` symlink loop in the main repo (a self-referential
symlink → `.lake -> /Users/.../proofs/.lake`) and the partial mathlib clone
that followed after removing it prevented `lake exe cache get` from
populating `.lake/packages/mathlib/lean-toolchain`. The Lean code itself is
straightforward (`Matrix.det_fin_four` expansion + `ring`) and should compile
once a clean worktree is available.

## Active Approach

Companion file `Proofs/ProductOfSegmentsOfChordsOQ03.lean` defining the $4 \times 4$
concyclicity determinant and proving the bidirectional concyclicity criterion via
Cramer's rule, then using it to discharge the parent axiom.

## Attempt Count

- Total attempts: 2 (S1 OBSERVE + S2 SCAFFOLD)
- Current approach attempts: 1
- Approaches tried: 1 (determinant + Cramer)

## Blockers

- **Local build infrastructure** (researcher-3 only): the worktree was wiped
  mid-build by a daemon respawn, and the main repo's `proofs/.lake` is a
  broken self-referential symlink. The next researcher should retry the
  docker build from a fresh worktree before committing further Lean work.

The mathematical strategy is otherwise unblocked. The approach is purely
algebraic and does not depend on Mathlib's `Affine.Simplex.circumcenter`
(which would otherwise require bridging `Vec2 := EuclideanSpace ℝ (Fin 2)`
with the `Affine.Simplex` API).

## Next Action

**S3 (any researcher)**: in `Proofs/ProductOfSegmentsOfChordsOQ03.lean`,
discharge the sorry in `concyclicityDet_eq_zero_iff_concyclic`. Concrete sub-tasks:

1. Replace the `hNonCollinear : True` placeholder with the real non-collinearity
   hypothesis (e.g. `¬ Collinear ℝ ({P₁, P₂, P₃} : Set Vec2)` or a stronger
   linear-independence form for the first three rows of the $3 \times 3$ minor).
2. Prove the (⇐) direction: $\Delta = 0$ together with non-collinearity yields
   $(D, E, F)$ via `Matrix.cramer`, define $O := (-D/2, -E/2)$ and
   $r := \sqrt{D^2/4 + E^2/4 - F}$, prove $r > 0$ from non-degeneracy, then
   verify $\|P_i - O\| = r$ for each $i$.

Target: 1 PR adding ~80 lines, no net change in sorry count (close the main
sorry, open one for the (⇒) direction handled in S4).

## Subsequent Plan

| Session | Goal | Lines | Sorries |
| --- | --- | --- | --- |
| S2 (done) | Define `concyclicityDet`, state main theorem with sorry. | 106 | +1 |
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
