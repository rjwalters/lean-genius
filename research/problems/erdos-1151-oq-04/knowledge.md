# Knowledge: erdos-1151-oq-04

## Problem Summary

**Goal**: Prove `erdos_1941_divergence` (axiom in `Erdos1151Problem.lean`) by formalizing
that the Chebyshev Lebesgue function Λₙ(cos(πp/q)) → ∞ for odd p, q, and then
constructing a continuous function whose Chebyshev interpolation diverges.

**Axiom to eliminate**:
```lean
axiom erdos_1941_divergence (p q : ℕ) (hp : Odd p) (hq : Odd q) (hq_pos : 0 < q) :
    let x := Real.cos (p * Real.pi / q)
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, M < chebyshevInterpSeq f x n
```

This says: for x = cos(πp/q), there EXISTS a continuous f such that Lₙf(x) → +∞ (full
sequence diverges to +∞, not just a subsequence).

## Architecture (Erdos1151OQ04.lean)

**Main reduction theorem** (COMPLETE, no sorry):
```
chebyshev_lebesgue_growth [sorry] + divergence_from_lebesgue_growth [sorry]
  → erdos_1941_divergence_from_growth [PROVED]
```

**Proved lemmas (no sorry)**:
- `lebesgue_upper_bound`: |Lₙf(x)| ≤ ‖f‖_∞ · Λₙ(x)
- `chebyshevInterp_add`, `chebyshevInterp_smul`: linearity
- `chebyshev_T_at_cos`: T_n(cos θ) = cos(nθ) [from Mathlib T_real_cos]
- `cos_int_pi`: cos(kπ) = (-1)^k [from Mathlib cos_int_mul_pi]
- `cos_rational_pi_at_multiples`: cos(mq·πp/q) = cos(mπp)
- `cos_rational_pi_nonzero_along_multiples`: along n = mq, cos(nπp/q) ≠ 0
- `chebyshevNode_mem_Icc`: nodes lie in [-1, 1]
- `abs_cos_int_pi_mul`: |cos(kπ)| = 1
- `chebyshevNode_is_root` (Session 2): T_n(cos φₖ) = 0
- `chebyshevNode_injective` (Session 2): Chebyshev nodes are distinct
- **`T_ofNat_ne_zero`** (Session 3): T_n ≠ 0 for n : ℕ
- **`natDegree_T_ofNat`** (Session 3): natDegree(T_n) = n for n : ℕ (by induction)
- **`leadingCoeff_T_ofNat`** (Session 3): leadingCoeff(T_n) = 2^{n-1} for n ≥ 1 (by induction)

**Aristotle companion (Erdos1151OQ04Aristotle.lean)** — all sorries CLOSED (Session 2):
- `cos_odd_half_pi`: cos((2k+1)π/2) = 0
- `chebyshevNode_is_root`: T_n at Chebyshev nodes = 0
- `chebyshevNode_injective`: nodes are distinct
- `n_mul_chebyshevAngle`, `chebyshevAngle_pos`, `chebyshevAngle_lt_pi`, etc. [arithmetic helpers]

## Hard Sorries Remaining (4 in main file)

### 1. `lagrange_basis_chebyshev_formula` [PARTIAL PROGRESS]
Requires: Chebyshev product formula T_n(x) = 2^{n-1}·Π_{k=0}^{n-1}(x - cos φₖ).
**NOT in Mathlib v4.26.0**, but now have the prerequisites:
- `T_ofNat_ne_zero` ✓
- `natDegree_T_ofNat` ✓  
- `leadingCoeff_T_ofNat` ✓
**Next**: Prove product formula using: T_n - 2^{n-1}·∏(X - cos φₖ) has degree < n with n roots → = 0.

### 2. `chebyshev_lebesgue_eq` [BLOCKED by #1]
Reduces Λₙ(cos θ) to a trigonometric sum. Follows from #1.

### 3. `chebyshev_lebesgue_growth` [BLOCKED by #1, #2]
Main result: Λₙ(cos(πp/q)) → ∞. Proof outline known:
- Along n = mq: |cos(nπp/q)| = 1 (already proved: cos_rational_pi_nonzero_along_multiples)
- Lower bound: Σₖ sin(φₖ)/|cos(πp/q) - cos φₖ| ≥ C·log(n)
- Blocked by needing formula from #1.

### 4. `divergence_from_lebesgue_growth` [OPEN, proof sketch has gap]
Statement: Λₙ(x) → ∞ ⟹ ∃ continuous f, Lₙf(x) → +∞.

Proof sketch in file gives lacunary construction: f = Σₖ (1/k²) fₙₖ.
**Gap**: Cross terms dominate: Σⱼ≠ₖ (1/j²) Λₙₖ(x) ≥ Λₙₖ(x)·(π²/6) >> Λₙₖ(x)/k².
Fix requires de-correlation: |Lₙₖ(fₙⱼ)(x)| << Λₙₖ(x) for nₖ >> nⱼ.
Estimated: 200+ lines, needs analysis of Chebyshev interpolation between different grids.

**Alternative**: Baire category gives lim sup = ∞, but NOT full divergence (lim = ∞).
May need to reconsider whether the axiom statement is too strong.

## Session 2026-04-23 — Results (Session 4)

**Outcome**: progress
**Sorries closed**: 0 (build fixes — Session 3 lemmas now compile)
**Build errors fixed** (Mathlib v4.26.0 API changes + proof bugs):
- `natDegree_T_ofNat | (n+2)`: `apply natDegree_sub_eq_left_of_natDegree_lt` failed (conclusion `p.natDegree` doesn't unify with `n+2`); fixed using `have key + rw`
- `chebyshevNode_is_root`: `field_simp; ring` — field_simp closes goal, `ring` had no goals; fixed by removing `ring`
- `chebyshevNode_injective`: `div_lt_iff` renamed to `div_lt_iff₀` in Mathlib v4.26.0; `nlinarith` then needed `omega` + `exact_mod_cast` to convert ℕ→ℝ strict bound before `nlinarith` for nonlinear finish

**Key technique learned**:
- When `apply lemma` fails "could not unify conclusion", use `have key := lemma proof; rw [key, ...]` instead
- `linarith` cannot multiply inequalities by variables (nonlinear); use `nlinarith` or provide product as hint `mul_lt_mul_of_pos_right`
- ℕ strict inequality `j.val < n` gives only `(j.val : ℝ) < n`, NOT `2 * j.val + 1 < 2 * n` in ℝ; must use `omega` first on ℕ, then `exact_mod_cast`

**PR**: rjwalters/lean-genius#11646 — all 3 Session 3 lemmas now build clean

## Session 2026-04-23 — Results (Session 3)

**Outcome**: progress  
**Sorries closed**: 0 (foundation proofs, not closing sorries directly)
**New proofs added** (prerequisites for product formula):
- `T_ofNat_ne_zero (n : ℕ) : T ℝ (n : ℤ) ≠ 0` — by T_eval_one
- `natDegree_T_ofNat : ∀ n : ℕ, (T ℝ (n : ℤ)).natDegree = n` — by two-step induction
- `leadingCoeff_T_ofNat : ∀ n ≥ 1, (T ℝ (n : ℤ)).leadingCoeff = 2^(n-1)` — by two-step induction

**Key proof techniques**:
- `T_ofNat_ne_zero`: `simp [T_eval_one h]` — T_n(1) = 1 ≠ 0
- `natDegree_T_ofNat`: two-step match, `natDegree_sub_eq_left_of_natDegree_lt` since deg(T_n) < deg(2X·T_{n+1})
- `leadingCoeff_T_ofNat`: two-step match, `leadingCoeff_sub_of_degree_lt` + `leadingCoeff_mul`; `(2 : ℝ[X]) = C 2` via `C_ofNat`

**Product formula proof strategy** (for next session):
Let Q_n = 2^{n-1} · ∏_{k : Fin n} (X - C (cos φₖ)).
Then T_n - Q_n has:
- natDegree ≤ n-1 (leading coefficients both 2^{n-1} cancel)
- n distinct roots: each cos φₖ is a root of T_n (chebyshevNode_is_root) and of Q_n
- A polynomial of degree < n with n distinct roots is zero (by card_roots_le_degree)
Therefore T_n = Q_n.

## Session 2026-04-22 — Results (Session 2)

**Outcome**: progress  
**Sorries closed**: 5 (chebyshevNode_is_root ×2, chebyshevNode_injective ×2, cos_odd_half_pi)
**Companion file**: now 0 sorries
**Main file**: 4 sorries remain (all blocked by Chebyshev product formula or hard lacunary construction)

**Key proofs**:
- `cos_odd_half_pi`: `rw [h, cos_add, cos_pi_div_two, mul_zero, sin_nat_mul_pi, ...]`
- `chebyshevNode_is_root`: simp [chebyshev_T_at_cos], arithmetic cast manipulation, cos_odd_half_pi
- `chebyshevNode_injective`: strictAntiOn_cos.injOn on angles in (0,π)

## Next Steps

1. **IMMEDIATE**: Prove the Chebyshev product formula using T_ofNat_ne_zero + natDegree_T_ofNat + leadingCoeff_T_ofNat (all now building):
   - Define Q_n = 2^{n-1} · ∏_{k : Fin n} (X - C (cos φₖ))
   - Show T_n - Q_n has natDegree ≤ n-1 (leadingCoeffs cancel: both = 2^{n-1})
   - Show T_n - Q_n has n distinct roots (chebyshevNode_is_root + chebyshevNode_injective)
   - Apply `Polynomial.card_roots_le_degree` to conclude T_n - Q_n = 0
   - This unblocks lagrange_basis_chebyshev_formula, chebyshev_lebesgue_eq, chebyshev_lebesgue_growth
2. Assess divergence_from_lebesgue_growth gap more carefully; consider Banach-Steinhaus
3. Mathlib v4.26.0 confirmed: no Chebyshev product formula; must build locally
