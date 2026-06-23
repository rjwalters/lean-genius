import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# Arithmetic Mean - Geometric Mean Inequality

## What This Proves
The AM-GM Inequality: For non-negative real numbers, the arithmetic mean is always
greater than or equal to the geometric mean, with equality if and only if all
the numbers are equal.

For two non-negative real numbers a and b:
  (a + b) / 2 ≥ √(ab)

For n non-negative real numbers a₁, ..., aₙ:
  (a₁ + ⋯ + aₙ) / n ≥ ⁿ√(a₁ ⋯ aₙ)

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `Real.geom_mean_le_arith_mean_weighted`
  for the general case and provide an elementary proof for the two-variable case.
- **Elementary Proof:** The two-variable case follows from (√a - √b)² ≥ 0, which
  expands to a - 2√(ab) + b ≥ 0, hence (a + b)/2 ≥ √(ab).
- **Key Insight:** The inequality follows from the non-negativity of squares.
- **Proof Techniques Demonstrated:** nlinarith for nonlinear arithmetic, calc chains,
  Finset manipulation, weighted means.

## Status
- [x] Complete proof
- [x] Uses Mathlib for general result
- [x] Elementary proof for two-variable case
- [x] Equality characterization
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Real.geom_mean_le_arith_mean_weighted` : General weighted AM-GM
- `Real.geom_mean_le_arith_mean2_weighted` : Weighted 2-variable AM-GM
- `Real.sqrt_mul` : √(ab) = √a · √b for a ≥ 0
- `Real.sq_sqrt` : (√a)² = a for a ≥ 0
- `sq_nonneg` : x² ≥ 0 for all x

## Historical Note
The AM-GM inequality has ancient origins, with geometric proofs dating to Euclid.
The general n-variable form was developed in the 19th century. It is fundamental to
optimization, economics, and information theory.

This is #38 on Wiedijk's list of 100 theorems.
-/

namespace AMGMInequality

/-! ## The Two-Variable Case (Elementary Proof)

The classical proof using (√a - √b)² ≥ 0.

This is the most intuitive approach: any square is non-negative, so
  (√a - √b)² ≥ 0
Expanding:
  a - 2√(ab) + b ≥ 0
  a + b ≥ 2√(ab)
  (a + b)/2 ≥ √(ab)
-/

/-- **AM-GM Inequality for two variables (Wiedijk #38)**

For non-negative real numbers a and b:
  (a + b) / 2 ≥ √(ab)

This is proven elementarily using the fact that (√a - √b)² ≥ 0. -/
theorem am_gm_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / 2 ≥ Real.sqrt (a * b) := by
  have h_sq_nonneg : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
  have h_expand : (Real.sqrt a - Real.sqrt b) ^ 2 =
      Real.sqrt a ^ 2 - 2 * Real.sqrt a * Real.sqrt b + Real.sqrt b ^ 2 := by ring
  rw [h_expand, Real.sq_sqrt ha, Real.sq_sqrt hb] at h_sq_nonneg
  have h_sqrt_mul : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) :=
    (Real.sqrt_mul ha b).symm
  linarith

/-- **AM-GM Inequality for two variables (Alternative form)**

Equivalent statement: a + b ≥ 2√(ab) for non-negative a, b. -/
theorem am_gm_two' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a + b ≥ 2 * Real.sqrt (a * b) := by
  have h := am_gm_two a b ha hb
  linarith

/-! ## Equality Characterization

The AM-GM inequality is an equality if and only if a = b. -/

/-- **AM-GM Equality Condition (Two Variables)**

(a + b) / 2 = √(ab) if and only if a = b.

The "if" direction is trivial. The "only if" direction follows from
(√a - √b)² = 0 implying √a = √b, hence a = b for non-negative a, b. -/
theorem am_gm_two_eq_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / 2 = Real.sqrt (a * b) ↔ a = b := by
  constructor
  · -- Forward: equality implies a = b
    intro h_eq
    -- We use the fact that (√a - √b)² ≥ 0 and the inequality is tight
    have h_sqrt_mul : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) :=
      (Real.sqrt_mul ha b).symm
    -- If (a + b)/2 = √(ab), then (√a - √b)² = 0
    have h_sq_zero : (Real.sqrt a - Real.sqrt b) ^ 2 = 0 := by
      have h_expand : (Real.sqrt a - Real.sqrt b) ^ 2 =
          a - 2 * Real.sqrt (a * b) + b := by
        calc (Real.sqrt a - Real.sqrt b) ^ 2
            = Real.sqrt a ^ 2 - 2 * Real.sqrt a * Real.sqrt b + Real.sqrt b ^ 2 := by ring
          _ = a - 2 * Real.sqrt a * Real.sqrt b + b := by
              rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
          _ = a - 2 * Real.sqrt (a * b) + b := by
              rw [← h_sqrt_mul]; ring
      rw [h_expand]
      linarith
    -- (√a - √b)² = 0 implies √a = √b
    have h_sqrt_eq : Real.sqrt a = Real.sqrt b := by
      have : Real.sqrt a - Real.sqrt b = 0 := pow_eq_zero h_sq_zero
      linarith
    -- √a = √b implies a = b for non-negative a, b
    calc a = Real.sqrt a ^ 2 := (Real.sq_sqrt ha).symm
      _ = Real.sqrt b ^ 2 := by rw [h_sqrt_eq]
      _ = b := Real.sq_sqrt hb
  · -- Backward: a = b implies equality
    intro h_eq
    rw [h_eq]
    have h_sq : b * b = b ^ 2 := by ring
    rw [h_sq, Real.sqrt_sq hb]
    ring

/-! ## General n-Variable AM-GM via Weighted Means

Using Mathlib's general weighted AM-GM inequality over Finsets. -/

/-- **Weighted AM-GM Inequality (General)**

For non-negative weights w summing to 1 and non-negative values z:
  ∏ᵢ zᵢ^wᵢ ≤ ∑ᵢ wᵢ · zᵢ

This is the weighted form where different values can have different weights. -/
theorem am_gm_weighted {ι : Type*} (s : Finset ι) (w z : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw_sum : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i :=
  Real.geom_mean_le_arith_mean_weighted s w z hw hw_sum hz

/-- **AM-GM for two variables via weighted means**

Setting w₁ = w₂ = 1/2 gives the unweighted two-variable AM-GM. -/
theorem am_gm_two_via_weighted (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ (1/2 : ℝ) * b ^ (1/2 : ℝ) ≤ (a + b) / 2 := by
  have h := Real.geom_mean_le_arith_mean2_weighted
    (by linarith : (0 : ℝ) ≤ 1/2)
    (by linarith : (0 : ℝ) ≤ 1/2)
    ha hb
    (by ring : (1/2 : ℝ) + 1/2 = 1)
  convert h using 1
  all_goals ring

/-! ## Examples and Verification -/

/-- AM-GM for equal numbers: (a + a)/2 = √(a·a) = a -/
example (a : ℝ) (ha : 0 ≤ a) : (a + a) / 2 = Real.sqrt (a * a) := by
  have h : a * a = a ^ 2 := by ring
  rw [h, Real.sqrt_sq ha]
  ring

/-- AM-GM strict inequality when a ≠ b -/
example : (1 + 4) / 2 > Real.sqrt (1 * 4) := by
  have : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_sq_eq (by linarith) (by linarith)]
    norm_num
  simp [this]
  norm_num

/-- Concrete example: AM-GM for 2 and 8 -/
example : (2 + 8) / 2 ≥ Real.sqrt (2 * 8) := by
  apply am_gm_two <;> linarith

/-! ## Corollaries and Applications -/

/-- **Product-Sum Inequality**

For non-negative a and b: ab ≤ ((a + b)/2)²

This follows directly from AM-GM by squaring both sides. -/
theorem product_le_mean_sq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ ((a + b) / 2) ^ 2 := by
  have h := am_gm_two a b ha hb
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  calc a * b = Real.sqrt (a * b) ^ 2 := (Real.sq_sqrt (mul_nonneg ha hb)).symm
    _ ≤ ((a + b) / 2) ^ 2 := sq_le_sq' (by linarith) h

/-- **Quadratic Mean ≥ Arithmetic Mean ≥ Geometric Mean**

For non-negative a, b: √((a² + b²)/2) ≥ (a + b)/2 ≥ √(ab)

Here we prove the AM ≥ GM part. -/
theorem am_ge_gm (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / 2 ≥ Real.sqrt (a * b) :=
  am_gm_two a b ha hb

/-- **Three-Variable AM-GM (via Mathlib)**

For non-negative a, b, c:
  (a + b + c) / 3 ≥ (abc)^(1/3) -/
theorem am_gm_three (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a ^ (1/3 : ℝ) * b ^ (1/3 : ℝ) * c ^ (1/3 : ℝ) ≤ (a + b + c) / 3 := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (by linarith : (0 : ℝ) ≤ 1/3)
    (by linarith : (0 : ℝ) ≤ 1/3)
    (by linarith : (0 : ℝ) ≤ 1/3)
    ha hb hc
    (by ring : (1/3 : ℝ) + 1/3 + 1/3 = 1)
  convert h using 1
  all_goals ring

#check am_gm_two
#check am_gm_two_eq_iff
#check am_gm_weighted
#check am_gm_three

end AMGMInequality
