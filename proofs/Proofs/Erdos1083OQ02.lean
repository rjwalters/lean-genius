/-
Erdős Problem #1083 OQ-02: Reducing the Solymosi-Vu Gap

Formalizes the known bounds on f_d(n), the minimum number of distinct
distances determined by n points in ℝ^d (d ≥ 3), focusing on the gap
between the Solymosi-Vu lower bound and the conjectured truth.

Known bounds:
- Lower: f_d(n) ≥ c · n^{2(d+1)/(d(d+2))} [Solymosi-Vu 2008]
- Upper: f_d(n) ≤ C · n^{2/d}              [integer lattice grid]
- Conjecture: f_d(n) = n^{2/d - o(1)}

The gap in the exponent is 2/(d(d+2)), which is O(1/d²).
Eliminating this gap is the content of Erdős Problem #1083.

References:
- https://erdosproblems.com/1083
- Solymosi, Vu (2008): "Near optimal bounds for the Erdős distinct
  distances problem in high dimensions" Combinatorica 28(1)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Erdos1083OQ02

/-
## The Distinct Distance Function
-/

/-- f_d(n): minimum number of distinct distances determined by any set
    of n points in ℝ^d. Axiomatized as an extremal quantity. -/
axiom f (d n : ℕ) : ℕ

/-
## Known Bounds
-/

/-- **Erdős (1946)**: f_d(n) ≥ c · n^{1/d}.
    Pigeonhole: n points with ≤ k distances → k^d ≥ n. -/
axiom erdos_lower (d : ℕ) (hd : d ≥ 3) :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      c * (n : ℝ) ^ ((1 : ℝ) / d) ≤ (f d n : ℝ)

/-- **Grid upper bound**: f_d(n) ≤ C · n^{2/d}.
    The integer lattice {1,...,k}^d has k^d points and O(k²) = O(n^{2/d})
    distinct distances. -/
axiom grid_upper (d : ℕ) (hd : d ≥ 3) :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (f d n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / d)

/-- **Solymosi-Vu (2008)**: f_d(n) ≥ c · n^{2(d+1)/(d(d+2))} for d ≥ 4.
    The exponent 2(d+1)/(d(d+2)) improves on Erdős's 1/d significantly.
    Uses incidence bounds and geometric partitioning. -/
axiom solymosi_vu (d : ℕ) (hd : d ≥ 4) :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      c * (n : ℝ) ^ (2 * (↑d + 1) / (↑d * (↑d + 2))) ≤ (f d n : ℝ)

/-
## Structural Analysis of the Gap

The SV exponent 2(d+1)/(d(d+2)) lies strictly between Erdős's
1/d and the conjectured 2/d. We prove this algebraically.
-/

/-- The SV exponent strictly improves on Erdős's lower bound exponent. -/
theorem sv_improves_erdos (d : ℕ) (hd : d ≥ 4) :
    (1 : ℝ) / d < 2 * (↑d + 1) / (↑d * (↑d + 2)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  rw [div_lt_div_iff hd_pos (mul_pos hd_pos hd2_pos)]
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

/-- The SV exponent is still below the conjectured 2/d. -/
theorem sv_below_conjecture (d : ℕ) (hd : d ≥ 4) :
    2 * (↑d + 1) / (↑d * (↑d + 2)) < (2 : ℝ) / d := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  rw [div_lt_div_iff (mul_pos hd_pos hd2_pos) hd_pos]
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

/-- The gap is 2/(d(d+2)).
    For d=4: 1/12. For d=10: 1/60. For d=100: 1/5100. -/
theorem gap_formula (d : ℕ) (hd : d ≥ 4) :
    (2 : ℝ) / d - 2 * (↑d + 1) / (↑d * (↑d + 2)) =
    2 / (↑d * (↑d + 2)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hd2_ne : (↑d : ℝ) * ((↑d : ℝ) + 2) ≠ 0 := ne_of_gt (mul_pos hd_pos hd2_pos)
  field_simp
  ring

/-- Concrete gap for d = 4: the gap is 1/12 ≈ 0.083. -/
theorem gap_d4 : (2 : ℝ) / (4 * (4 + 2)) = 1 / 12 := by norm_num

/-- Concrete gap for d = 10: the gap is 1/60 ≈ 0.017. -/
theorem gap_d10 : (2 : ℝ) / (10 * (10 + 2)) = 1 / 60 := by norm_num

/-
## Structural Properties of the Gap
-/

/-- The SV exponent equals the fraction (d+1)/(d+2) of the conjectured exponent.
    This reveals the obstruction clearly: the SV technique captures all but
    a 1/(d+2) fraction of the conjectured bound. -/
theorem sv_fraction_of_conjecture (d : ℕ) (hd : d ≥ 4) :
    2 * ((↑d : ℝ) + 1) / ((↑d : ℝ) * ((↑d : ℝ) + 2)) =
    (((↑d : ℝ) + 1) / ((↑d : ℝ) + 2)) * (2 / (↑d : ℝ)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  have hd_ne : (↑d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hd2_ne : (↑d : ℝ) + 2 ≠ 0 := ne_of_gt hd2_pos
  field_simp
  ring

/-- The fraction (d+1)/(d+2) is strictly less than 1, confirming that
    the SV bound falls short of the conjectured exponent 2/d. -/
theorem sv_fraction_lt_one (d : ℕ) (hd : d ≥ 4) :
    ((↑d : ℝ) + 1) / ((↑d : ℝ) + 2) < 1 := by
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) d; linarith
  rw [div_lt_one hd2_pos]
  linarith [Nat.cast_nonneg (α := ℝ) d]

/-- For d ≥ 3, the gap 2/(d(d+2)) exceeds 1/d².
    This shows the gap decays no faster than 1/d² — it persists at quadratic rate. -/
theorem gap_exceeds_reciprocal_sq (d : ℕ) (hd : d ≥ 3) :
    1 / (↑d : ℝ) ^ 2 < 2 / ((↑d : ℝ) * ((↑d : ℝ) + 2)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  rw [div_lt_div_iff (pow_pos hd_pos 2) (mul_pos hd_pos hd2_pos)]
  nlinarith [Nat.cast_nonneg (α := ℝ) d, sq_nonneg (↑d : ℝ)]

/-- The gap 2/(d(d+2)) is always less than 2/d².
    Combined with gap_exceeds_reciprocal_sq: 1/d² < gap < 2/d² for d ≥ 3. -/
theorem gap_below_twice_reciprocal_sq (d : ℕ) (hd : d ≥ 1) :
    2 / ((↑d : ℝ) * ((↑d : ℝ) + 2)) < 2 / (↑d : ℝ) ^ 2 := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  rw [div_lt_div_iff (mul_pos hd_pos hd2_pos) (pow_pos hd_pos 2)]
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

/-- The gap 2/(d(d+2)) is strictly decreasing in d.
    As d grows, the SV bound converges toward the conjectured exponent.
    Proof: (d+1)(d+3) - d(d+2) = 2d+3 > 0. -/
theorem gap_strictly_decreasing (d : ℕ) (hd : d ≥ 4) :
    2 / (((↑d : ℝ) + 1) * ((↑d : ℝ) + 3)) < 2 / ((↑d : ℝ) * ((↑d : ℝ) + 2)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  have hd3_pos : (0 : ℝ) < (↑d : ℝ) + 3 := by linarith
  have h1_pos : (0 : ℝ) < (↑d : ℝ) + 1 := by linarith
  rw [div_lt_div_iff (mul_pos h1_pos hd3_pos) (mul_pos hd_pos hd2_pos)]
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

/-- The SV fraction (d+1)/(d+2) is itself strictly increasing in d,
    confirming that higher dimensions get a proportionally tighter bound. -/
theorem sv_fraction_increasing (d : ℕ) (hd : d ≥ 4) :
    ((↑d : ℝ) + 1) / ((↑d : ℝ) + 2) < ((↑d : ℝ) + 2) / ((↑d : ℝ) + 3) := by
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) d; linarith
  have hd3_pos : (0 : ℝ) < (↑d : ℝ) + 3 := by linarith
  rw [div_lt_div_iff hd2_pos hd3_pos]
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

/-- Concrete SV fraction for d = 4: achieves 5/6 ≈ 83.3% of conjectured exponent. -/
theorem sv_fraction_d4 : ((4 : ℝ) + 1) / ((4 : ℝ) + 2) = 5 / 6 := by norm_num

/-- Concrete SV fraction for d = 10: achieves 11/12 ≈ 91.7% of conjectured exponent. -/
theorem sv_fraction_d10 : ((10 : ℝ) + 1) / ((10 : ℝ) + 2) = 11 / 12 := by norm_num

/-
## Progress Fraction Analysis

We quantify what fraction of the full Erdős→conjecture gap the SV method closes.

The Erdős exponent is 1/d, the conjectured exponent is 2/d (gap = 1/d).
The SV improvement over Erdős is 2(d+1)/(d(d+2)) - 1/d = 1/(d+2).
So SV covers (1/(d+2)) / (1/d) = d/(d+2) of the full gap.
-/

/-- The SV improvement over Erdős's bound is exactly 1/(d+2).
    SV exponent - Erdős exponent = 2(d+1)/(d(d+2)) - 1/d = 1/(d+2). -/
theorem sv_improvement_over_erdos (d : ℕ) (hd : d ≥ 4) :
    2 * ((↑d : ℝ) + 1) / ((↑d : ℝ) * ((↑d : ℝ) + 2)) - 1 / (↑d : ℝ) =
    1 / ((↑d : ℝ) + 2) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  have hd_ne : (↑d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hd2_ne : (↑d : ℝ) + 2 ≠ 0 := ne_of_gt hd2_pos
  have hprod_ne : (↑d : ℝ) * ((↑d : ℝ) + 2) ≠ 0 := mul_ne_zero hd_ne hd2_ne
  field_simp
  ring

/-- The total gap from Erdős to the conjectured exponent is 1/d.
    Conjectured exponent - Erdős exponent = 2/d - 1/d = 1/d. -/
theorem erdos_to_conjecture_gap (d : ℕ) (hd : d ≥ 4) :
    (2 : ℝ) / (↑d : ℝ) - 1 / (↑d : ℝ) = 1 / (↑d : ℝ) := by
  ring

/-- The SV method closes exactly d/(d+2) of the full gap from Erdős to conjecture.
    Progress fraction = (SV improvement) / (total gap) = (1/(d+2)) / (1/d) = d/(d+2).
    For d=4: 4/6 = 2/3 ≈ 66.7%. For d=10: 10/12 = 5/6 ≈ 83.3%.
    Note: complements sv_fraction_of_conjecture (which measures SV/conjecture directly). -/
theorem sv_covers_d_over_d_plus_2_of_total_gap (d : ℕ) (hd : d ≥ 4) :
    (2 * ((↑d : ℝ) + 1) / ((↑d : ℝ) * ((↑d : ℝ) + 2)) - 1 / (↑d : ℝ)) /
    (2 / (↑d : ℝ) - 1 / (↑d : ℝ)) = (↑d : ℝ) / ((↑d : ℝ) + 2) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  have hd_ne : (↑d : ℝ) ≠ 0 := ne_of_gt hd_pos
  have hd2_ne : (↑d : ℝ) + 2 ≠ 0 := ne_of_gt hd2_pos
  have hprod_ne : (↑d : ℝ) * ((↑d : ℝ) + 2) ≠ 0 := mul_ne_zero hd_ne hd2_ne
  field_simp
  ring

/-- Concrete progress fractions at specific dimensions.
    d=4: SV closes 2/3 of the gap. d=10: SV closes 5/6 of the gap. -/
theorem sv_progress_fraction_d4 :
    (4 : ℝ) / ((4 : ℝ) + 2) = 2 / 3 := by norm_num

theorem sv_progress_fraction_d10 :
    (10 : ℝ) / ((10 : ℝ) + 2) = 5 / 6 := by norm_num

/-- The remaining open gap (as a fraction of Erdős→conjecture gap) is 2/(d+2),
    strictly decreasing toward 0. The problem is asymptotically negligible
    as d → ∞, but still significant for small dimensions. -/
theorem sv_remaining_gap_fraction (d : ℕ) (hd : d ≥ 4) :
    1 - (↑d : ℝ) / ((↑d : ℝ) + 2) = 2 / ((↑d : ℝ) + 2) := by
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) d; linarith
  field_simp
  ring

/-
## The Conjecture
-/

/-- **Erdős Conjecture #1083**: f_d(n) = n^{2/d - o(1)}.
    Eliminating the SV gap entirely would prove this. -/
axiom erdos_1083_conjecture (d : ℕ) (hd : d ≥ 3) :
    ∀ ε : ℝ, ε > 0 →
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      c * (n : ℝ) ^ ((2 : ℝ) / d - ε) ≤ (f d n : ℝ)

/-
## Summary

State of Erdős #1083:
- Erdős (1946): exponent 1/d
- Solymosi-Vu (2008): exponent 2(d+1)/(d(d+2))
- Conjecture: exponent 2/d - o(1)
- Gap: 2/(d(d+2)) = O(1/d²)

Axiom count: 5 (f, erdos_lower, grid_upper, solymosi_vu, conjecture)
Sorry count: 0
Proved: 19 theorems (gap analysis, exponent comparison, structural properties, progress fractions)

Key structural results:
- sv_fraction_of_conjecture: SV exponent = (d+1)/(d+2) · (2/d)
- gap_exceeds_reciprocal_sq + gap_below_twice_reciprocal_sq: 1/d² < gap < 2/d²
- gap_strictly_decreasing: gap(d) > gap(d+1) (converges to 0)
- sv_fraction_increasing: (d+1)/(d+2) strictly increases toward 1
- sv_improvement_over_erdos: SV improvement over Erdős = 1/(d+2)
- sv_covers_d_over_d_plus_2_of_total_gap: SV closes d/(d+2) of full Erdős→conjecture gap
- sv_remaining_gap_fraction: remaining open fraction = 2/(d+2)

The gap 2/(d(d+2)) is precisely characterized: it lies in (1/d², 2/d²),
strictly decreases with d, and vanishes asymptotically.
The SV method closes d/(d+2) of the Erdős→conjecture gap (e.g., 2/3 for d=4, 5/6 for d=10).
No known approach eliminates the remaining 2/(d+2) fraction for any fixed d ≥ 4.
-/

end Erdos1083OQ02
