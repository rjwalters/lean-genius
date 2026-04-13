# Lebesgue Measure OQ-03-OQ-01: Impossibility of Translation-Invariant Measures

**Status**: IN PROGRESS (ACT phase)
**Problem**: Formalize the impossibility of a nonzero translation-invariant locally finite Borel measure on an infinite-dimensional Hilbert space.

## Problem Summary

**Parent**: `lebesgue-measure-oq-03` — proved `orthonormal_dist` (‖eₙ - eₘ‖ = √2) and `orthonormal_balls_disjoint` (√2 > 2/3) as supporting lemmas.

**Question**: Can the full impossibility theorem be formalized using Mathlib's MeasureTheory infrastructure? The argument is elementary but requires formalizing infinite disjoint families of sets with the same measure.

**Key argument**:
- Orthonormal sequence {eₙ} has ‖eₙ‖ = 1, ⟪eₙ, eₘ⟫ = 0 for n ≠ m
- Balls B(eₙ, 1/3) are pairwise disjoint (distance √2 > 2/3)
- All contained in B(0, 4/3) (since ‖eₙ‖ = 1)
- Translation invariance → all have equal measure c = μ(B(0, 1/3))
- N * c ≤ μ(B(0, 4/3)) < ∞ for all N → c = 0 by Archimedean property

---

## Session 2026-04-12 (Session 1)

**Mode**: FRESH (first session on this problem)
**Outcome**: progress — built `LebesgueMeasureOQ03OQ01.lean` from scratch (196 lines, 0 sorries)

### What I Did

1. Read `LebesgueMeasureOQ03.lean` — identified `orthonormal_dist` and `orthonormal_balls_disjoint` as available supporting lemmas
2. Designed 5-part proof structure: Archimedean → core measure lemma → translation invariance → orthonormal infrastructure → main theorem
3. Implemented all parts

### Key Mathematical Findings

**`ennreal_const_le_finite_imp_zero`**: ENNReal Archimedean property.
- Case `c = ⊤`: 1 * ⊤ = ⊤ ≤ M < ⊤, contradiction
- Case 0 < c < ⊤: Use `ENNReal.exists_nat_gt` (M / c < N), then M = (M/c)*c < N*c via `ENNReal.div_mul_cancel₀`

**`zero_measure_of_infinite_disjoint`**: The core lemma. N * μ(f 0) = μ(⋃_{n<N} f n) ≤ μ(S) via `measure_biUnion_finset`. Apply Archimedean.

**`IsTransInvariant`**: Defined as `∀ v, μ.map (fun x => x + v) = μ`.

**`trans_inv_ball_eq`**: μ(ball x r) = μ(ball 0 r). Key: `(· + -x)⁻¹' ball(0,r) = ball(x,r)` since `dist(y + -x, 0) = ‖y - x‖ = dist(y, x)`.

**`OrthoSeq`**: Structure with `seq`, `norm_one`, `inner_zero`.

**`ortho_balls_disjoint`**: Uses `orthonormal_dist` and `orthonormal_balls_disjoint` from parent.

**`no_invariant_locally_finite_ball`**: Combines all pieces.

### Files Created

- `proofs/Proofs/LebesgueMeasureOQ03OQ01.lean` (196 lines, 8 lemmas/defs, 0 sorries claimed)
- `proofs/Proofs.lean` (updated with import)
- `src/data/research/problems/lebesgue-measure-oq-03-oq-01.json` (updated)

### Potential Issues / Build Notes

Several lemmas rely on specific Mathlib 4 API names:
- `ENNReal.div_mul_cancel₀` — division-multiplication cancellation (might be `ENNReal.div_mul_cancel`)
- `ENNReal.mul_lt_mul_right'` — strict multiplication monotone (might need different name)
- `ENNReal.exists_nat_gt` — Archimedean for ENNReal
- `measure_biUnion_finset` — finite disjoint union measure
- `ENNReal.div_lt_top` — finiteness of division

Build verification needed once Docker is available. If build fails on specific lemma names, fallback to sorries for those steps.

### Next Steps

1. **Immediate**: Verify build once Docker Desktop is available
2. Search Mathlib for exact names of `ENNReal.div_mul_cancel₀` and `ENNReal.mul_lt_mul_right'`
3. If build fails, add sorries for the failing ENNReal steps and submit to Aristotle
4. Consider extending to the full theorem: μ = 0 on all Borel sets (not just balls)
