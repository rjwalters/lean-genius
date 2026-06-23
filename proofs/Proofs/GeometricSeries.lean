import Mathlib.Algebra.GeomSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Sum of a Geometric Series

## What This Proves
The sum formula for geometric series—both finite and infinite cases:

**Finite sum**: For r ≠ 1:
  ∑_{k=0}^{n-1} r^k = (1 - r^n) / (1 - r)

**Infinite sum**: For |r| < 1:
  ∑_{k=0}^{∞} r^k = 1 / (1 - r)

The general case with first term a:
  ∑_{k=0}^{∞} a·r^k = a / (1 - r)

## Approach
- **Foundation (from Mathlib):** We use `mul_neg_geom_sum` for the finite case
  and `tsum_geometric_of_abs_lt_one` for the infinite series convergence.
- **Key Insight:** The finite formula follows from multiplying S_n by r and subtracting.
  The infinite case follows by taking the limit as n → ∞ when |r| < 1.
- **Proof Techniques Demonstrated:** Ring operations, limits, series convergence.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main results
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `mul_neg_geom_sum` : Finite geometric sum formula
- `tsum_geometric_of_abs_lt_one` : Infinite geometric series sum
- `summable_geometric_of_abs_lt_one` : Geometric series is summable

## Historical Note
Geometric series have been studied since antiquity. Archimedes used a geometric
series to find the area under a parabola. The formula for infinite geometric
series was formalized in the 17th century, though the concept of convergence
wasn't rigorously defined until the 19th century.

This is #66 on Wiedijk's list of 100 theorems.
-/

namespace GeometricSeries

open Finset BigOperators

/-! ## Finite Geometric Sum

The classic formula for the sum of a finite geometric progression. -/

/-- **Finite Geometric Sum Formula (Wiedijk #66)**

For any ring element r and natural number n:
  (1 - r) * ∑_{k=0}^{n-1} r^k = 1 - r^n

This fundamental identity arises from the telescoping that occurs when
multiplying the sum by (1 - r). -/
theorem finite_geom_sum {R : Type*} [Ring R] (r : R) (n : ℕ) :
    (1 - r) * ∑ k in range n, r ^ k = 1 - r ^ n :=
  mul_neg_geom_sum r n

/-- The finite sum in the form (sum) * (1 - r) = 1 - r^n -/
theorem finite_geom_sum' {R : Type*} [Ring R] (r : R) (n : ℕ) :
    (∑ k in range n, r ^ k) * (1 - r) = 1 - r ^ n :=
  _root_.geom_sum_mul_neg r n

/-- Alternate form: the sum equals (1 - r^n) / (1 - r) when r ≠ 1 -/
theorem finite_geom_sum_div {R : Type*} [DivisionRing R] (r : R) (n : ℕ) (hr : r ≠ 1) :
    ∑ k in range n, r ^ k = (1 - r ^ n) / (1 - r) := by
  have h1r : 1 - r ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr hr)
  field_simp
  exact _root_.geom_sum_mul_neg r n

/-! ## Infinite Geometric Series

For |r| < 1, the infinite geometric series converges to 1/(1-r). -/

/-- **Infinite Geometric Series Sum (Wiedijk #66)**

For real r with |r| < 1:
  ∑_{k=0}^{∞} r^k = (1 - r)⁻¹

This is perhaps the most important infinite series formula, with
applications throughout analysis, probability, and physics. -/
theorem infinite_geom_sum (r : ℝ) (hr : |r| < 1) :
    ∑' k : ℕ, r ^ k = (1 - r)⁻¹ :=
  tsum_geometric_of_abs_lt_one hr

/-- The geometric series is summable when |r| < 1 -/
theorem geom_series_summable (r : ℝ) (hr : |r| < 1) :
    Summable (fun n : ℕ => r ^ n) :=
  summable_geometric_of_abs_lt_one hr

/-! ## General Form with First Term

When the first term is a (not necessarily 1): -/

/-- **General Infinite Geometric Series**

For first term a and ratio r with |r| < 1:
  ∑_{k=0}^{∞} a·r^k = a * (1 - r)⁻¹ -/
theorem infinite_geom_sum_scaled (a r : ℝ) (hr : |r| < 1) :
    ∑' k : ℕ, a * r ^ k = a * (1 - r)⁻¹ := by
  simp only [tsum_mul_left, infinite_geom_sum r hr]

/-! ## Special Cases and Examples -/

/-- Sum of 1/2 + 1/4 + 1/8 + ... = 1

A classic example: repeatedly halving gives a total of 1. -/
theorem sum_halves : ∑' k : ℕ, (1/2 : ℝ) ^ (k + 1) = 1 := by
  have h : |(1/2 : ℝ)| < 1 := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    norm_num
  calc ∑' k : ℕ, (1/2 : ℝ) ^ (k + 1)
      = ∑' k : ℕ, (1/2) * (1/2 : ℝ) ^ k := by simp only [pow_succ']
    _ = (1/2) * ∑' k : ℕ, (1/2 : ℝ) ^ k := by rw [tsum_mul_left]
    _ = (1/2) * (1 - 1/2)⁻¹ := by rw [infinite_geom_sum (1/2) h]
    _ = 1 := by norm_num

/-- Geometric series with r = 1/3 sums to 3/2 -/
theorem geom_sum_third : ∑' k : ℕ, (1/3 : ℝ) ^ k = 3/2 := by
  have h : |(1/3 : ℝ)| < 1 := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/3)]
    norm_num
  rw [infinite_geom_sum (1/3) h]
  norm_num

/-- Geometric series with r = -1/2 (alternating) sums to 2/3 -/
theorem geom_sum_neg_half : ∑' k : ℕ, (-1/2 : ℝ) ^ k = 2/3 := by
  have h : |(-1/2 : ℝ)| < 1 := by
    have : (-1/2 : ℝ) = -(1/2) := by ring
    rw [this, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    norm_num
  rw [infinite_geom_sum (-1/2) h]
  norm_num

/-! ## Connection to Finite Sums

The infinite sum is the limit of finite partial sums. -/

/-- Finite sums approach the infinite sum -/
theorem finite_to_infinite (r : ℝ) (hr : |r| < 1) :
    Filter.Tendsto (fun n => ∑ k in range n, r ^ k)
      Filter.atTop (nhds ((1 - r)⁻¹)) := by
  have hs : Summable (fun n : ℕ => r ^ n) := geom_series_summable r hr
  have hsum : ∑' k : ℕ, r ^ k = (1 - r)⁻¹ := infinite_geom_sum r hr
  rw [← hsum]
  exact HasSum.tendsto_sum_nat hs.hasSum

/-! ## Verification Examples -/

/-- Verify: 1 + 2 + 4 + 8 + 16 = 31 = (32 - 1)/(2 - 1) -/
example : (∑ k in range 5, (2 : ℕ) ^ k) = 31 := by native_decide

/-- Verify: 1 + 3 + 9 + 27 = 40 = (81 - 1)/(3 - 1) -/
example : (∑ k in range 4, (3 : ℕ) ^ k) = 40 := by native_decide

/-- Verify: 1 + 1/2 + 1/4 + 1/8 = 15/8 -/
example : (∑ k in range 4, (1/2 : ℚ) ^ k) = 15/8 := by native_decide

#check finite_geom_sum
#check infinite_geom_sum
#check geom_series_summable

end GeometricSeries
