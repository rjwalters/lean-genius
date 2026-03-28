import Mathlib

/-
# Matching Lower Bound for Birthday Problem (OQ-02-OQ-01)

## What This Proves
Formalizes the matching lower bound for the Birthday Problem:

  P(all distinct) ≥ exp(-k(k-1)/(2d) - k²(k-1)²/(4d²))

Combined with the upper bound from OQ-02 (P(all distinct) ≤ exp(-k(k-1)/(2d))),
this gives a two-sided exponential approximation for the birthday collision probability.

## Key Mathematical Idea
For 0 ≤ x < 1, we have ln(1-x) ≥ -x - x² (a consequence of the Taylor series).
Applied to each factor (1 - i/d) in P(all distinct) = ∏(1-i/d):

  ln(∏(1-i/d)) = ∑ ln(1-i/d) ≥ ∑(-i/d - i²/d²) = -k(k-1)/(2d) - S₂/d²

where S₂ = ∑ i² = k(k-1)(2k-1)/6 ≤ k²(k-1)²/4.

## Approach
- **Foundation:** The key inequality ln(1-x) ≥ -x - x² for 0 ≤ x < 1
- **Product bound:** Apply to each factor and sum logarithms
- **Exponentiate:** Obtain the exponential lower bound on the product
-/

open Finset Real

/- ## Core Inequality: ln(1-x) ≥ -x - x² for 0 ≤ x < 1 -/

/-- For 0 ≤ x < 1, we have 1 - x ≥ exp(-x - x²).
    Equivalently, ln(1-x) ≥ -x - x². This is the key ingredient
    for the matching lower bound.

    Proof strategy: We need exp(-x - x²) ≤ 1 - x, i.e.,
    exp(-x(1+x)) ≤ 1 - x. -/
theorem exp_neg_sub_sq_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.exp (-x - x ^ 2) ≤ 1 - x := by
  sorry -- Deep analytic inequality; candidate for Aristotle or manual Taylor argument

/-- The product formula for the probability that k items are all distinct
    among d possibilities. P(all distinct) = ∏_{i=0}^{k-1} (1 - i/d). -/
noncomputable def birthdayProduct (k d : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, (1 - (i : ℝ) / (d : ℝ))

/-- Each factor in the birthday product is nonneg when k ≤ d + 1. -/
theorem birthdayProduct_factor_nonneg {k d : ℕ} (hd : 0 < d) (hk : k ≤ d + 1)
    (i : ℕ) (hi : i ∈ Finset.range k) : 0 ≤ 1 - (i : ℝ) / (d : ℝ) := by
  rw [Finset.mem_range] at hi
  have : (i : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : i ≤ d)
  have hid : (i : ℝ) / (d : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hd : (0 : ℝ) < d)]
    exact this
  linarith

/-- Each factor in the birthday product is at most 1. -/
theorem birthdayProduct_factor_le_one {d : ℕ} (hd : 0 < d)
    (i : ℕ) : 1 - (i : ℝ) / (d : ℝ) ≤ 1 := by
  have : 0 ≤ (i : ℝ) / (d : ℝ) := div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg d)
  linarith

/-- The birthday product is nonneg when k ≤ d + 1. -/
theorem birthdayProduct_nonneg {k d : ℕ} (hd : 0 < d) (hk : k ≤ d + 1) :
    0 ≤ birthdayProduct k d :=
  Finset.prod_nonneg (fun i hi => birthdayProduct_factor_nonneg hd hk i hi)

/- ## Sum of squares bound -/

/-- The sum ∑_{i<k} i² = k(k-1)(2k-1)/6. -/
theorem sum_sq_formula (k : ℕ) :
    6 * ∑ i ∈ Finset.range k, (i : ℝ) ^ 2 = (k : ℝ) * (k - 1) * (2 * k - 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    linarith

/-- Bound: ∑_{i<k} i² ≤ k²(k-1)²/4 for k ≥ 1.
    (This follows from k(k-1)(2k-1)/6 ≤ k²(k-1)²/4, i.e., 2(2k-1)/3 ≤ k(k-1).) -/
theorem sum_sq_le_quartic (k : ℕ) (hk : 1 ≤ k) :
    ∑ i ∈ Finset.range k, (i : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 * (k - 1) ^ 2 / 4 := by
  sorry -- Arithmetic from sum_sq_formula; needs nlinarith with specific case analysis

/- ## Main Lower Bound -/

/-- **Main Theorem**: Birthday product lower bound.
    P(all distinct) ≥ exp(-k(k-1)/(2d) - k²(k-1)²/(4d²))
    for 1 ≤ k ≤ d + 1, d ≥ 1.

    This is the matching lower bound for the OQ-02 upper bound:
    P(all distinct) ≤ exp(-k(k-1)/(2d)). -/
theorem birthdayProduct_lower_bound {k d : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : k ≤ d + 1) :
    Real.exp (-(k : ℝ) * (k - 1) / (2 * d) - (k : ℝ) ^ 2 * (k - 1) ^ 2 / (4 * (d : ℝ) ^ 2))
      ≤ birthdayProduct k d := by
  sorry -- Follows from exp_neg_sub_sq_le_one_sub applied to each factor,
        -- then sum_sq_le_quartic for the quadratic correction term

/-- The two-sided bound: combining with the upper bound from OQ-02,
    P(all distinct) is sandwiched between two exponentials.
    This gives a precise asymptotic: P(all distinct) ≈ exp(-k(k-1)/(2d)). -/
theorem birthdayProduct_two_sided {k d : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : k ≤ d + 1) :
    Real.exp (-(k : ℝ) * (k - 1) / (2 * d) - (k : ℝ) ^ 2 * (k - 1) ^ 2 / (4 * (d : ℝ) ^ 2))
      ≤ birthdayProduct k d ∧
    birthdayProduct k d ≤ Real.exp (-(k : ℝ) * (k - 1) / (2 * d)) := by
  exact ⟨birthdayProduct_lower_bound hd hk hkd, by
    -- Upper bound from OQ-02 (Erdős-style: 1-x ≤ exp(-x))
    unfold birthdayProduct
    calc ∏ i ∈ Finset.range k, (1 - (i : ℝ) / d)
        ≤ ∏ i ∈ Finset.range k, Real.exp (-(i : ℝ) / d) := by
          apply Finset.prod_le_prod
            (fun i hi => birthdayProduct_factor_nonneg (by omega) hkd i hi)
          intro i _
          have h := add_one_le_exp (-↑i / (↑d : ℝ))
          have : -↑i / (↑d : ℝ) + 1 = 1 - ↑i / ↑d := by ring
          linarith
      _ = Real.exp (∑ i ∈ Finset.range k, (-(↑i : ℝ) / ↑d)) := by
          rw [Real.exp_sum]
      _ = Real.exp (-(↑k : ℝ) * (↑k - 1) / (2 * ↑d)) := by
          congr 1; sorry -- Gauss sum arithmetic
  ⟩
