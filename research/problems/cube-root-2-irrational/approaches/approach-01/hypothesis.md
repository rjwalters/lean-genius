# Hypothesis: Not-Integer Approach (via irrational_nrt_of_notint_nrt)

**Approach ID**: approach-01
**Problem**: cube-root-2-irrational
**Created**: 2025-12-30
**Status**: SUCCESS ✓

## The Conjecture

Use Mathlib's `irrational_nrt_of_notint_nrt` theorem to prove ∛2 is irrational.

### Proof Strategy

The theorem states: If x^n = m (integer) and x is not an integer, then x is irrational.

For ∛2:
1. Let x = 2^(1/3), n = 3, m = 2
2. x³ = 2 ✓
3. x is not an integer (because 2 is not a perfect cube) ✓
4. Therefore x is irrational ✓

## Key Lemmas

### Lemma 1: 2^(1/3)³ = 2

**Statement**: `((2 : ℝ) ^ (1/3 : ℝ)) ^ 3 = 2`

**Approach**:
```lean
rw [← Real.rpow_natCast]
rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
norm_num
```

**Status**: ✓ PROVEN

### Lemma 2: 2 is not a perfect cube

**Statement**: `¬ ∃ (n : ℤ), n ^ 3 = 2`

**Approach**: Bound analysis with nlinarith
- n ≤ 0 → n³ ≤ 0 < 2 (use n³ = n*n*n for nlinarith)
- n ≥ 2 → n³ ≥ 8 > 2 (same approach)
- n = 1 → 1³ = 1 ≠ 2

**Status**: ✓ PROVEN

### Lemma 3: cbrt2 is not an integer

**Statement**: `¬ ∃ (n : ℤ), cbrt2 = n`

**Approach**: If cbrt2 = n, then n³ = cbrt2³ = 2, contradicting Lemma 2

**Status**: ✓ PROVEN

## Technical Requirements

### Mathlib Dependencies

- `Mathlib.Data.Real.Irrational` — `irrational_nrt_of_notint_nrt`
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — `Real.rpow_mul`
- `Mathlib.Tactic` — `nlinarith`, `omega`, `norm_num`

### Key Tactic Insight

The main challenge was proving cubic bounds on integers. The solution:
- `nlinarith` doesn't handle `n ^ 3` well
- Rewrite `n ^ 3 = n * n * n` using `ring` tactic
- Then `nlinarith` can handle the product

## Risk Assessment

### What Could Go Wrong

1. ~~**Type coercion issues**: Converting between ℝ, ℤ, ℕ~~ — Handled with exact_mod_cast
2. ~~**rpow vs pow mismatch**: `Real.rpow` might not match `HPow.hPow`~~ — Handled with Real.rpow_natCast
3. ~~**Cubic bounds**: nlinarith doesn't handle powers~~ — Rewrite to products

### Adversarial Attacks Tried

1. [x] Verify x^3 = 2 actually type-checks — YES
2. [x] Check the exact signature of theorem — Used correct arguments
3. [x] Verify bound computation works — nlinarith with n*n*n

## Origins

### Where This Idea Came From

- **Inspiration**: Web search for Mathlib irrationality theorems
- **Strategy type**: Direct application of existing theorem
- **Related successful proof**: sqrt2-irrational uses similar approach

### Why It Worked

1. Mathlib had the exact theorem we needed
2. The "not-integer" formulation was simpler than multiplicity
3. Bound analysis with nlinarith avoided complex interval tactics

## Attempt Log

| Attempt | Date | Result | Key Insight |
|---------|------|--------|-------------|
| 1 | 2025-12-30 | SUCCESS | Use nlinarith with n*n*n rewrite for cubic bounds |

## Notes

This proof pattern generalizes to any ∛m where m is not a perfect cube:
- Define the n-th root as `m ^ (1/n : ℝ)`
- Prove `(m ^ (1/n))^n = m` using rpow_mul
- Prove m is not a perfect n-th power by bound analysis
- Apply irrational_nrt_of_notint_nrt
