# Mean Value Theorem OQ-04: FTC via MVT Structure

**Status**: IN PROGRESS (ACT phase)
**Problem**: Formalize the Fundamental Theorem of Calculus and show the MVT-FTC structural duality.

## Problem Summary

**Parent**: `mean-value-theorem-oq-03` — proved vector-valued MVT inequality via Mathlib's `norm_image_sub_le_of_norm_deriv_le_segment'`.

**Question**: What is the cleanest formalization of FTC using the MVT structure? Show:
1. FTC Part 1: F(x) = ∫ₐˣ f ⟹ F'(x) = f(x)
2. FTC Part 2 (Newton-Leibniz): ∫ₐᵇ F' = F(b) - F(a)
3. MVT from FTC: ∫ₐᵇ f'/(b-a) = f'(c) for some c (IVT on continuous f')
4. Integration by parts from product rule + FTC
5. Uniqueness: F' = G' and F(a) = G(a) ⟹ F = G

## Session 2026-04-12 (Session 1)

**Mode**: FRESH (first session on this problem)
**Outcome**: progress — built `MeanValueTheoremOQ04.lean` (~310 lines, 14 theorems, 0 sorries)

### What I Did

1. Read `MeanValueTheoremOQ03.lean` — parent providing `exists_deriv_eq_slope` (MVT)
2. Designed the MVT-FTC duality structure
3. Implemented all parts using Mathlib's FTC infrastructure

### Key Mathematical Findings

**MVT-FTC Duality**:
- MVT: f(b)-f(a) = f'(c)·(b-a) for some c — existence via IVT
- FTC: f(b)-f(a) = ∫ₐᵇ f' dt — exact integral formula
- Connection: MVT follows from FTC by taking c = integral average witness via IVT

**ftc_uniqueness proof strategy**: 
- h = F - G has h' = f - f = 0 everywhere
- Newton-Leibniz: ∫ₐˣ 0 dt = h(x) - h(a)
- So 0 = h(x) - 0, giving F(x) = G(x)
- For `y ∈ uIcc a x → y ∈ uIcc a b`: explicit case analysis over 4 branches

**Mathlib API notes**:
- FTC Part 1: `intervalIntegral.integral_hasDerivAt_right` needs `stronglyMeasurableAtFilter` argument (via `ContinuousAt.stronglyMeasurableAtFilter`)
- Newton-Leibniz: `integral_eq_sub_of_hasDerivAt` — clean one-liner
- MVT: `exists_deriv_eq_slope` — already in parent chain
- Integration by parts: `integral_add` + `integral_eq_sub_of_hasDerivAt`

### Files Created

- `proofs/Proofs/MeanValueTheoremOQ04.lean` (~310 lines, 14 theorems, 0 sorries)
- `src/data/research/problems/mean-value-theorem-oq-04.json` (created)
- Created this knowledge.md file

### Potential Issues / Build Notes

- `intervalIntegral.integral_hasDerivAt_right` — need to verify exact arg list
- `Icc_subset_uIcc` — should exist but verify
- `mem_uIcc` unfolding for set containment — may need simp lemmas

### Next Steps

1. Build verification once Docker available
2. Check if `stronglyMeasurableAtFilter` needs different form
3. Consider Lebesgue integral version of FTC
