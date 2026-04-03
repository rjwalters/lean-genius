/-
# Unified Faulhaber Formula via Bernoulli Numbers (OQ-01)

## Research Question
Can the general Faulhaber formula
  ∑_{i=0}^{n-1} i^k = (1/(k+1)) ∑_{j=0}^{k} C(k+1,j) · B_j · n^{k+1-j}
be formalized in Lean using Mathlib's Bernoulli infrastructure, proving
all power sum formulas (k=1,...,5) as special cases of a single unified identity?

## Answer: YES

`Finset.sum_range_pow n k` is exactly this unified formula. Every specific
Faulhaber formula (sum of squares, cubes, etc.) is a single computation:
substitute Bernoulli numbers and simplify via ring.

## Key Ingredients
- `Finset.sum_range_pow n k` — the general formula in Mathlib
- B₀=1, B₁=-1/2, B₂=1/6, B₃=0, B₄=-1/30, B₅=0 (Bernoulli numbers)
- `linear_combination` for polynomial identity verification

## Method
For each k, we:
1. Apply `Finset.sum_range_pow` (the unified formula)
2. Unfold the finite sum (j = 0, ..., k) via `simp`
3. Substitute known Bernoulli values
4. Normalize coercions and arithmetic with `norm_num`
5. Close by `linear_combination h` (polynomial identity via ring)

This is pure computation from the unified formula — NO induction needed.

## Remark on Notation
Sums are over `range n`, so `∑ i ∈ range n, i^k = ∑_{i=0}^{n-1} i^k`.
Example: `∑_{i<4} i^2 = 0+1+4+9 = 14 = 4·3·7/6`.
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Tactic

open Finset BigOperators

namespace FaulhaberUnified

/-! ## The Unified Faulhaber Formula -/

/-- **Unified Faulhaber Formula**: The sum of k-th powers is a polynomial in n
    expressed via Bernoulli numbers.
    This single identity subsumes ALL specific power sum formulas. -/
theorem faulhaber_unified (n k : ℕ) :
    ∑ i ∈ range n, (i : ℚ) ^ k =
    ∑ j ∈ range (k + 1),
      bernoulli j * ↑((k + 1).choose j) * (n : ℚ) ^ (k + 1 - j) / (↑k + 1) :=
  sum_range_pow n k

/-! ## Bernoulli Number Values -/

private lemma hB2 : bernoulli 2 = (1 / 6 : ℚ) := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : (2 : ℕ) ≠ 1)]
  exact bernoulli'_two

private lemma hB3 : bernoulli 3 = (0 : ℚ) :=
  bernoulli_eq_zero_of_odd (by decide) (by decide)

private lemma hB4 : bernoulli 4 = (-1 / 30 : ℚ) := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : (4 : ℕ) ≠ 1)]
  exact bernoulli'_four

private lemma hB5 : bernoulli 5 = (0 : ℚ) :=
  bernoulli_eq_zero_of_odd (by decide) (by decide)

/-! ## Specific Formulas as Special Cases of the Unified Identity -/

/-- **k=1**: Sum of first powers via the unified formula.
    ∑_{i<n} i = n(n-1)/2.
    Computation: B₀·C(2,0)·n²/2 + B₁·C(2,1)·n/2 = n²/2 - n/2 = n(n-1)/2. -/
theorem sum_pow1_from_faulhaber (n : ℕ) :
    ∑ i ∈ range n, (i : ℚ) ^ 1 = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  have h := faulhaber_unified n 1
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_one] at h ⊢
  rw [bernoulli_zero, bernoulli_one] at h
  norm_num at h
  rw [h]; ring

/-- **k=2**: Sum of squares via the unified formula.
    ∑_{i<n} i² = n(n-1)(2n-1)/6.
    Computation: B₀·n³/3 + B₁·3n²/3 + B₂·3n/3
               = n³/3 - n²/2 + n/6 = n(n-1)(2n-1)/6. -/
theorem sum_pow2_from_faulhaber (n : ℕ) :
    ∑ i ∈ range n, (i : ℚ) ^ 2 =
    (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6 := by
  have h := faulhaber_unified n 2
  simp only [sum_range_succ, sum_range_zero, zero_add] at h
  rw [bernoulli_zero, bernoulli_one, hB2] at h
  norm_num at h
  rw [h]; ring

/-- **k=3**: Sum of cubes via the unified formula.
    ∑_{i<n} i³ = n²(n-1)²/4.
    Computation: B₀·n⁴/4 + B₁·4n³/4 + B₂·6n²/4 + B₃·n/4
               = n⁴/4 - n³/2 + n²/4 = n²(n-1)²/4. -/
theorem sum_pow3_from_faulhaber (n : ℕ) :
    ∑ i ∈ range n, (i : ℚ) ^ 3 =
    (n : ℚ) ^ 2 * ((n : ℚ) - 1) ^ 2 / 4 := by
  have h := faulhaber_unified n 3
  simp only [sum_range_succ, sum_range_zero, zero_add] at h
  simp only [show Nat.choose 4 0 = 1 from rfl, show Nat.choose 4 1 = 4 from rfl,
             show Nat.choose 4 2 = 6 from rfl, show Nat.choose 4 3 = 4 from rfl,
             Nat.cast_one, Nat.cast_ofNat] at h
  rw [bernoulli_zero, bernoulli_one, hB2, hB3] at h
  norm_num at h
  rw [h]; ring

/-- **k=4**: Sum of fourth powers via the unified formula.
    ∑_{i<n} i⁴ = n(n-1)(2n-1)(3n²-3n-1)/30.
    Computation: B₀·n⁵/5 + B₁·5n⁴/5 + B₂·10n³/5 + B₃·0 + B₄·5n/5
               = n⁵/5 - n⁴/2 + n³/3 - n/30 = n(n-1)(2n-1)(3n²-3n-1)/30. -/
theorem sum_pow4_from_faulhaber (n : ℕ) :
    ∑ i ∈ range n, (i : ℚ) ^ 4 =
    (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) *
    (3 * (n : ℚ) ^ 2 - 3 * (n : ℚ) - 1) / 30 := by
  have h := faulhaber_unified n 4
  simp only [sum_range_succ, sum_range_zero, zero_add] at h
  simp only [show Nat.choose 5 0 = 1 from rfl, show Nat.choose 5 1 = 5 from rfl,
             show Nat.choose 5 2 = 10 from rfl, show Nat.choose 5 3 = 10 from rfl,
             show Nat.choose 5 4 = 5 from rfl,
             Nat.cast_one, Nat.cast_ofNat] at h
  rw [bernoulli_zero, bernoulli_one, hB2, hB3, hB4] at h
  norm_num at h
  rw [h]; ring

/-- **k=5**: Sum of fifth powers via the unified formula.
    ∑_{i<n} i⁵ = n²(n-1)²(2n²-2n-1)/12.
    Computation: B₀·n⁶/6 + B₁·6n⁵/6 + B₂·15n⁴/6 + B₃·0 + B₄·15n²/6 + B₅·n/6
               = n⁶/6 - n⁵/2 + 5n⁴/12 - n²/12 = n²(n-1)²(2n²-2n-1)/12. -/
theorem sum_pow5_from_faulhaber (n : ℕ) :
    ∑ i ∈ range n, (i : ℚ) ^ 5 =
    (n : ℚ) ^ 2 * ((n : ℚ) - 1) ^ 2 *
    (2 * (n : ℚ) ^ 2 - 2 * (n : ℚ) - 1) / 12 := by
  have h := faulhaber_unified n 5
  simp only [sum_range_succ, sum_range_zero, zero_add] at h
  simp only [show Nat.choose 6 0 = 1 from rfl, show Nat.choose 6 1 = 6 from rfl,
             show Nat.choose 6 2 = 15 from rfl, show Nat.choose 6 3 = 20 from rfl,
             show Nat.choose 6 4 = 15 from rfl, show Nat.choose 6 5 = 6 from rfl,
             Nat.cast_one, Nat.cast_ofNat] at h
  rw [bernoulli_zero, bernoulli_one, hB2, hB3, hB4, hB5] at h
  norm_num at h
  rw [h]; ring

/-! ## The Completeness Theorem

All five specific power sum formulas follow from the single unified identity. -/

/-- **Main Result**: The Faulhaber formula for k ∈ {1,2,3,4,5}
    follows purely from the unified Bernoulli identity — no induction needed.

    This answers OQ-01: the general formula
      ∑_{i=0}^{n-1} i^k = (1/(k+1)) ∑_{j=0}^{k} C(k+1,j) B_j n^{k+1-j}
    can be formalized in Lean using Mathlib's Bernoulli infrastructure,
    and all specific formulas are special cases. -/
theorem faulhaber_completeness :
    (∀ n : ℕ, ∑ i ∈ range n, (i : ℚ)^1 = n * (n - 1) / 2) ∧
    (∀ n : ℕ, ∑ i ∈ range n, (i : ℚ)^2 = n * (n - 1) * (2 * n - 1) / 6) ∧
    (∀ n : ℕ, ∑ i ∈ range n, (i : ℚ)^3 = n^2 * (n - 1)^2 / 4) ∧
    (∀ n : ℕ, ∑ i ∈ range n, (i : ℚ)^4 = n * (n-1) * (2*n-1) * (3*n^2 - 3*n - 1) / 30) ∧
    (∀ n : ℕ, ∑ i ∈ range n, (i : ℚ)^5 = n^2 * (n-1)^2 * (2*n^2 - 2*n - 1) / 12) :=
  ⟨sum_pow1_from_faulhaber, sum_pow2_from_faulhaber, sum_pow3_from_faulhaber,
   sum_pow4_from_faulhaber, sum_pow5_from_faulhaber⟩

/-! ## Numerical Verification -/

/-- Verify k=2 at n=4: 0+1+4+9 = 14 = 4·3·7/6 -/
example : ∑ i ∈ range 4, (i : ℚ)^2 = 14 := by
  simp only [sum_range_succ, sum_range_zero]
  norm_num

/-- Verify k=3 at n=4: 0+1+8+27 = 36 = 16·9/4 -/
example : ∑ i ∈ range 4, (i : ℚ)^3 = 36 := by
  simp only [sum_range_succ, sum_range_zero]
  norm_num

/-- Verify k=4 at n=4: 0+1+16+81 = 98 = 4·3·7·23/30 -/
example : ∑ i ∈ range 4, (i : ℚ)^4 = 98 := by
  simp only [sum_range_succ, sum_range_zero]
  norm_num

/-- Verify k=5 at n=4: 0+1+32+243 = 276 = 16·9·23/12 -/
example : ∑ i ∈ range 4, (i : ℚ)^5 = 276 := by
  simp only [sum_range_succ, sum_range_zero]
  norm_num

end FaulhaberUnified
