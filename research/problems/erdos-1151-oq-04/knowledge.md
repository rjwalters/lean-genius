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
- **chebyshevNode_is_root** (PROVED this session): T_n(cos φₖ) = 0
- **chebyshevNode_injective** (PROVED this session): Chebyshev nodes are distinct

**Aristotle companion (Erdos1151OQ04Aristotle.lean)** — all sorries CLOSED this session:
- `cos_odd_half_pi`: cos((2k+1)π/2) = 0
- `chebyshevNode_is_root`: T_n at Chebyshev nodes = 0
- `chebyshevNode_injective`: nodes are distinct
- `n_mul_chebyshevAngle`, `chebyshevAngle_pos`, `chebyshevAngle_lt_pi`, etc. [arithmetic helpers]

## Hard Sorries Remaining (4 in main file)

### 1. `lagrange_basis_chebyshev_formula` [BLOCKED]
Requires: Chebyshev product formula T_n(x) = 2^{n-1}·Π_{k=0}^{n-1}(x - cos φₖ).
**NOT in Mathlib v4.26.0**. This blocks lemmas 2 and 3.

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
**Gap**: Cross terms in the lacunary series can dominate: Σⱼ≠ₖ (1/j²) Λₙₖ(x) ≥ Λₙₖ(x)·(π²/6-1/k²) >> Λₙₖ(x)/k².
Fix requires de-correlation: |Lₙₖ(fₙⱼ)(x)| << Λₙₖ(x) for nₖ >> nⱼ.
Estimated: 200+ lines, needs analysis of Chebyshev interpolation between different grids.

**Alternative**: Baire category gives lim sup = ∞, but NOT full divergence (lim = ∞).
May need to reconsider whether the axiom statement is too strong.

## Session 2026-04-22 — Results

**Outcome**: progress  
**Sorries closed**: 5 (chebyshevNode_is_root ×2, chebyshevNode_injective ×2, cos_odd_half_pi)
**Companion file**: now 0 sorries
**Main file**: 4 sorries remain (all blocked by Chebyshev product formula or hard lacunary construction)

**Key proofs**:
- `cos_odd_half_pi`: `rw [h, cos_add, cos_pi_div_two, mul_zero, sin_nat_mul_pi, ...]`
- `chebyshevNode_is_root`: simp [chebyshev_T_at_cos], arithmetic cast manipulation, cos_odd_half_pi
- `chebyshevNode_injective`: strictAntiOn_cos.injOn on angles in (0,π)

## Next Steps

1. Check if Mathlib v4.27+ adds the Chebyshev product formula
2. Consider building the product formula locally (~100-150 lines, tractable)
3. Assess whether `divergence_from_lebesgue_growth` as stated is provable (vs. lim sup version)
4. Alternative: Baire category argument for weaker divergence statement
