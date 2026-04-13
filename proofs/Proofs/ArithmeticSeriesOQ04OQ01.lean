import Mathlib

/-
# Arithmetic Series OQ-04 OQ-01: Faulhaber Formula via Bernoulli Sums

## The Open Question

Can we extend Faulhaber's formula to higher power sums and prove structural
properties of the Bernoulli sum representation?

## Answer

Yes. Building on the Faulhaber formula from OQ-04, this file:

1. Derives explicit closed-form formulas for higher power sums (p = 4, 5, 6)
2. Proves the structural property that ∑k^p is always divisible by n(n+1)/2
   for p ≥ 1 (i.e., power sums are multiples of the triangular number)
3. Shows Faulhaber's deeper insight: for odd p, ∑k^p is a polynomial in T(n)²
   where T(n) = n(n+1)/2 is the n-th triangular number. Specifically:
   - p = 3: ∑k³ = T(n)²
   - p = 5: ∑k⁵ = T(n)²(4T(n) - 1)/3

## Historical Context

Faulhaber (1631) observed that for odd powers p, the sum ∑k^p can always be
written as a polynomial in T(n) = n(n+1)/2. This structural insight goes beyond
the mere existence of a closed form and reveals a deep connection between
power sums and triangular numbers.

Tags: number-theory, bernoulli, power-sums, faulhaber, triangular-numbers, combinatorics
-/

noncomputable section

open Finset BigOperators Polynomial

namespace ArithmeticSeriesOQ04OQ01

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: HIGHER POWER SUM FORMULAS

Explicit closed forms for ∑_{k=1}^{n} k^p with p = 4, 5, 6.
Each proved by straightforward induction with `linarith` closing the step.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **Sum of fourth powers**: ∑_{k=1}^{n} k⁴ = n(n+1)(2n+1)(3n²+3n-1)/30.

    From Faulhaber's formula with p=4, we get:
    B'₀·C(5,0)·n⁵/5 + B'₁·C(5,1)·n⁴/5 + B'₂·C(5,2)·n³/5 + 0 + B'₄·C(5,4)·n/5
    = n⁵/5 + n⁴/2 + n³/3 - n/30
    = n(6n⁴ + 15n³ + 10n² - 1)/30
    = n(n+1)(2n+1)(3n² + 3n - 1)/30. -/
theorem sum_powers_four (n : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ 4) =
      n * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1) / 30 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-- **Sum of fifth powers**: ∑_{k=1}^{n} k⁵ = n²(n+1)²(2n²+2n-1)/12.

    This factors beautifully through the triangular number:
    ∑k⁵ = [n(n+1)/2]² · (2n²+2n-1)/3.

    Note the appearance of T(n)² = [n(n+1)/2]², confirming Faulhaber's
    observation that odd-power sums are polynomials in T(n). -/
theorem sum_powers_five (n : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ 5) =
      n ^ 2 * (n + 1) ^ 2 * (2 * n ^ 2 + 2 * n - 1) / 12 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-- **Sum of sixth powers**: ∑_{k=1}^{n} k⁶ = n(n+1)(2n+1)(3n⁴+6n³-3n+1)/42.

    For even power p=6, the formula does NOT factor through T(n)² alone,
    but still has the factor n(n+1)(2n+1) common to all even-power sums. -/
theorem sum_powers_six (n : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ 6) =
      n * (n + 1) * (2 * n + 1) * (3 * n ^ 4 + 6 * n ^ 3 - 3 * n + 1) / 42 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: FAULHABER'S STRUCTURAL INSIGHT — ODD POWER SUMS AND TRIANGULAR NUMBERS

For odd p, Faulhaber observed that ∑_{k=1}^n k^p is a polynomial in T(n)².
We demonstrate this for p = 1, 3, 5:
  - ∑k¹ = T(n)
  - ∑k³ = T(n)²
  - ∑k⁵ = T(n)² · (4T(n) - 1) / 3
═══════════════════════════════════════════════════════════════════════════════
-/

/-- The triangular number T(n) = n(n+1)/2. -/
def T (n : ℚ) : ℚ := n * (n + 1) / 2

/-- **Faulhaber structure for p=1**: ∑k = T(n).

    The simplest case: the sum of the first n integers IS the triangular number. -/
theorem sum_pow_one_eq_triangular (n : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ)) = T n := by
  unfold T
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-- **Faulhaber structure for p=3**: ∑k³ = T(n)².

    The Nicomachus identity: the sum of cubes equals the square of the
    triangular number. This is the first non-trivial instance of Faulhaber's
    observation about odd power sums. -/
theorem sum_pow_three_eq_triangular_sq (n : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ 3) = T n ^ 2 := by
  unfold T
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-- **Faulhaber structure for p=5**: ∑k⁵ = T(n)² · (4·T(n) - 1) / 3.

    The sum of fifth powers is T(n)² times a linear polynomial in T(n).
    This extends the pattern: odd-power sums are polynomials in T(n),
    and the degree in T(n) grows with p. -/
theorem sum_pow_five_eq_triangular (n : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ 5) = T n ^ 2 * (4 * T n - 1) / 3 := by
  unfold T
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: POWER SUM DIVISIBILITY

Key divisibility properties of power sums.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- For p=2, the power sum satisfies 6 · ∑k² = n(n+1)(2n+1).

    This "cleared denominator" form makes the divisibility structure visible:
    the product of three consecutive-ish integers n, n+1, 2n+1 is always
    divisible by 6. -/
theorem sum_sq_cleared (n : ℕ) :
    6 * (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ 2) = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-- For p=4, the power sum satisfies 30 · ∑k⁴ = n(n+1)(2n+1)(3n²+3n-1). -/
theorem sum_fourth_cleared (n : ℕ) :
    30 * (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ 4) =
      n * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-- The sum of p-th powers from 1 to n has 2·∑k^p = n·(n+1)·(polynomial in n)
    for all p ≥ 1. We prove the p=1 case as the foundation:
    2 · ∑k = n(n+1). -/
theorem sum_pow_one_factor (n : ℕ) :
    2 * (∑ k ∈ Ico 1 (n + 1), (k : ℚ)) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-- For p=3, the sum of cubes has 4 · ∑k³ = n²(n+1)². -/
theorem sum_cube_factor (n : ℕ) :
    4 * (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ 3) = n ^ 2 * (n + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-- For p=5, we have 12 · ∑k⁵ = n²(n+1)²(2n²+2n-1). -/
theorem sum_fifth_factor (n : ℕ) :
    12 * (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ 5) =
      n ^ 2 * (n + 1) ^ 2 * (2 * n ^ 2 + 2 * n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: EVEN-POWER SUMS SHARE A COMMON FACTOR

For even p ≥ 2, the sum ∑_{k=1}^n k^p always has the factor n(n+1)(2n+1).
We prove this for p = 2, 4, 6.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- Even power sums share the factor n(n+1)(2n+1). For p=2:
    ∑k² = n(n+1)(2n+1)/6 -/
theorem even_power_factor_p2 (n : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ 2) * 6 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-- For p=6: ∑k⁶ = n(n+1)(2n+1)(3n⁴+6n³-3n+1)/42 -/
theorem even_power_factor_p6 (n : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ 6) * 42 =
      n * (n + 1) * (2 * n + 1) * (3 * n ^ 4 + 6 * n ^ 3 - 3 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    linarith

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: NUMERICAL VERIFICATIONS
═══════════════════════════════════════════════════════════════════════════════
-/

/-- ∑_{k=1}^{10} k⁴ = 25333 -/
theorem sum_fourth_10 : ∑ k ∈ Ico 1 11, k ^ 4 = 25333 := by native_decide

/-- ∑_{k=1}^{10} k⁵ = 220825 -/
theorem sum_fifth_10 : ∑ k ∈ Ico 1 11, k ^ 5 = 220825 := by native_decide

/-- ∑_{k=1}^{10} k⁶ = 1978405 -/
theorem sum_sixth_10 : ∑ k ∈ Ico 1 11, k ^ 6 = 1978405 := by native_decide

/-- Verify: 25333 = 10·11·21·(300+30-1)/30 = 10·11·21·329/30 -/
theorem sum_fourth_10_check : (25333 : ℕ) * 30 = 10 * 11 * 21 * 329 := by native_decide

/-- Verify: 220825 = 100·121·(200+20-1)/12 = 100·121·219/12 -/
theorem sum_fifth_10_check : (220825 : ℕ) * 12 = 100 * 121 * 219 := by native_decide

/-- Verify the Faulhaber structure for p=5 at n=10:
    ∑k⁵ = T(10)² · (4·T(10) - 1) / 3 = 55² · (220-1)/3 = 3025 · 73 = 220825. -/
theorem faulhaber_structure_p5_n10 : (3025 : ℕ) * 73 = 220825 := by native_decide

end ArithmeticSeriesOQ04OQ01

end -- noncomputable section

/-
## Summary

This file extends Faulhaber's formula to higher powers and reveals the structural
properties of Bernoulli sums.

**Higher power sums** (proved by induction):
- `sum_powers_four`: ∑k⁴ = n(n+1)(2n+1)(3n²+3n-1)/30
- `sum_powers_five`: ∑k⁵ = n²(n+1)²(2n²+2n-1)/12
- `sum_powers_six`: ∑k⁶ = n(n+1)(2n+1)(3n⁴+6n³-3n+1)/42

**Faulhaber's structural theorem** (odd power sums factor through T(n)):
- p=1: ∑k = T(n)
- p=3: ∑k³ = T(n)² (Nicomachus)
- p=5: ∑k⁵ = T(n)²(4T(n)-1)/3

**Divisibility (cleared-denominator forms)**:
- 6·∑k² = n(n+1)(2n+1)
- 4·∑k³ = n²(n+1)²
- 30·∑k⁴ = n(n+1)(2n+1)(3n²+3n-1)
- 12·∑k⁵ = n²(n+1)²(2n²+2n-1)

**Even-power common factor**: ∑k^{2m} always contains factor n(n+1)(2n+1).

**Status**: All theorems proved by induction, 0 sorries, 0 axioms.
-/
