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
## Progress Analysis: How Far SV Reaches

The Erdős bound (1946) sets a baseline of 1/d.
The conjecture aims for 2/d.
SV (2008) achieves 2(d+1)/(d(d+2)).

We quantify exactly what fraction of the exponent gap SV covers.
-/

/-- The SV bound covers fraction d/(d+2) of the exponent gap from
    Erdős's 1946 bound to the conjecture.

    Formally: (SV - Erdős) / (Conjecture - Erdős) = d/(d+2).
    For d=4: 2/3 ≈ 67%. For d=10: 5/6 ≈ 83%. As d→∞: approaches 100%. -/
theorem sv_progress_fraction (d : ℕ) (hd : d ≥ 4) :
    (2 * (↑d + 1) / (↑d * (↑d + 2)) - 1 / ↑d) / (2 / ↑d - 1 / ↑d) =
    (↑d : ℝ) / (↑d + 2) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
  have hd2_ne : (↑d : ℝ) + 2 ≠ 0 := hd2_pos.ne'
  field_simp [hd_ne, hd2_ne]
  ring

/-- The relative gap — the fraction of the conjectured exponent not yet achieved
    by SV — equals exactly 1/(d+2).
    For d=4: 1/6 ≈ 17%. For d=10: 1/12 ≈ 8%. -/
theorem relative_gap_formula (d : ℕ) (hd : d ≥ 4) :
    (2 / ↑d - 2 * (↑d + 1) / (↑d * (↑d + 2))) / (2 / ↑d) =
    1 / ((↑d : ℝ) + 2) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
  have hd2_ne : (↑d : ℝ) + 2 ≠ 0 := hd2_pos.ne'
  field_simp [hd_ne, hd2_ne]
  ring

/-- Concrete progress for d=4: SV covers 2/3 of the exponent gap. -/
theorem progress_d4 : (4 : ℝ) / (4 + 2) = 2 / 3 := by norm_num

/-- Concrete progress for d=10: SV covers 5/6 of the exponent gap. -/
theorem progress_d10 : (10 : ℝ) / (10 + 2) = 5 / 6 := by norm_num

/-- Relative gap for d=4: the remaining fraction toward conjecture is 1/6. -/
theorem relative_gap_d4 : 1 / ((4 : ℝ) + 2) = 1 / 6 := by norm_num

/-- Relative gap for d=10: the remaining fraction toward conjecture is 1/12. -/
theorem relative_gap_d10 : 1 / ((10 : ℝ) + 2) = 1 / 12 := by norm_num

/-
## Near-Optimality in High Dimensions
-/

/-- For all d ≥ 2, SV covers at least half the exponent gap.
    Proof: d/(d+2) ≥ 1/2 ↔ 2d ≥ d+2 ↔ d ≥ 2. -/
theorem sv_covers_majority (d : ℕ) (hd : d ≥ 2) :
    (d : ℝ) / (↑d + 2) ≥ 1 / 2 := by
  have hd_cast : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  rw [ge_iff_le, div_le_div_iff (by norm_num : (0 : ℝ) < 2) hd2_pos]
  linarith

/-- For d ≥ 10, SV covers at least 5/6 of the exponent gap.
    Proof: d/(d+2) ≥ 5/6 ↔ 6d ≥ 5(d+2) ↔ d ≥ 10. -/
theorem sv_covers_five_sixths (d : ℕ) (hd : d ≥ 10) :
    (d : ℝ) / (↑d + 2) ≥ 5 / 6 := by
  have hd_cast : (10 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  rw [ge_iff_le, div_le_div_iff (by norm_num : (0 : ℝ) < 6) hd2_pos]
  linarith

/-- The relative gap 1/(d+2) is monotone decreasing: higher dimension → smaller gap. -/
theorem relative_gap_decreasing (d₁ d₂ : ℕ) (h : d₁ ≤ d₂) (hd1 : d₁ ≥ 4) :
    1 / ((d₂ : ℝ) + 2) ≤ 1 / ((d₁ : ℝ) + 2) := by
  have hd1_pos : (0 : ℝ) < (d₁ : ℝ) + 2 := by
    have : (0 : ℝ) < (d₁ : ℝ) := Nat.cast_pos.mpr (by omega)
    linarith
  have hd2_pos : (0 : ℝ) < (d₂ : ℝ) + 2 := by
    have h12 : (d₁ : ℝ) ≤ (d₂ : ℝ) := Nat.cast_le.mpr h
    linarith
  rw [div_le_div_iff hd2_pos hd1_pos]
  have h12 : (d₁ : ℝ) ≤ (d₂ : ℝ) := Nat.cast_le.mpr h
  linarith

/-
## Quadratic Bounds on the Gap

The absolute gap 2/(d(d+2)) satisfies tight bounds:
  1/d² < 2/(d(d+2)) < 2/d²
Together these show the gap is exactly of order 1/d².
-/

/-- The gap strictly exceeds 1/d² for d ≥ 3.
    Proof: 2/(d(d+2)) > 1/d² ⟺ 2d² > d(d+2) ⟺ d² > 2d ⟺ d > 2. -/
theorem gap_exceeds_reciprocal_sq (d : ℕ) (hd : d ≥ 3) :
    1 / (↑d : ℝ) ^ 2 < 2 / ((↑d : ℝ) * (↑d + 2)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  have hd3 : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  rw [div_lt_div_iff (pow_pos hd_pos 2) (mul_pos hd_pos hd2_pos)]
  have hmul : (0 : ℝ) < (↑d : ℝ) * ((↑d : ℝ) - 2) := mul_pos hd_pos (by linarith)
  nlinarith [hmul]

/-- The gap is strictly below 2/d² for d ≥ 1.
    Proof: 2/(d(d+2)) < 2/d² ⟺ d² < d(d+2) ⟺ 0 < 2d. -/
theorem gap_below_twice_reciprocal_sq (d : ℕ) (hd : d ≥ 1) :
    2 / ((↑d : ℝ) * (↑d + 2)) < 2 / (↑d : ℝ) ^ 2 := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  rw [div_lt_div_iff (mul_pos hd_pos hd2_pos) (pow_pos hd_pos 2)]
  nlinarith

/-- The absolute gap 2/(d(d+2)) is strictly decreasing in d.
    Proof: (d+1)(d+3) > d(d+2) since 2d+3 > 0. -/
theorem gap_strictly_decreasing (d : ℕ) (hd : d ≥ 4) :
    2 / ((↑d + 1 : ℝ) * (↑d + 3)) < 2 / ((↑d : ℝ) * (↑d + 2)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  have hd1_pos : (0 : ℝ) < (↑d : ℝ) + 1 := by linarith
  have hd3_pos : (0 : ℝ) < (↑d : ℝ) + 3 := by linarith
  rw [div_lt_div_iff (mul_pos hd1_pos hd3_pos) (mul_pos hd_pos hd2_pos)]
  nlinarith

/-
## Factored Structure of the SV Exponent
-/

/-- The SV exponent factors as (d+1)/(d+2) · (2/d).
    This reveals that SV achieves fraction (d+1)/(d+2) of the conjectured
    exponent, with the factor approaching 1 as d → ∞. -/
theorem sv_fraction_of_conjecture (d : ℕ) (hd : d ≥ 4) :
    2 * (↑d + 1) / (↑d * (↑d + 2)) = (↑d + 1) / (↑d + 2) * (2 / ↑d) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  have hd2_ne : (↑d : ℝ) + 2 ≠ 0 := hd2_pos.ne'
  field_simp
  ring

/-- The fraction (d+1)/(d+2) is strictly increasing in d.
    Proof: (d+1)(d+3) < (d+2)² ⟺ d²+4d+3 < d²+4d+4 ⟺ 3 < 4. -/
theorem sv_fraction_increasing (d : ℕ) :
    (↑d + 1) / (↑d + 2 : ℝ) < (↑d + 2) / (↑d + 3) := by
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hd2_pos : (0 : ℝ) < (↑d : ℝ) + 2 := by linarith
  have hd3_pos : (0 : ℝ) < (↑d : ℝ) + 3 := by linarith
  rw [div_lt_div_iff hd2_pos hd3_pos]
  nlinarith

/-- The SV fraction at d=4: (4+1)/(4+2) = 5/6. -/
theorem sv_fraction_d4 : (4 + 1 : ℝ) / (4 + 2) = 5 / 6 := by norm_num

/-- The SV fraction at d=10: (10+1)/(10+2) = 11/12. -/
theorem sv_fraction_d10 : (10 + 1 : ℝ) / (10 + 2) = 11 / 12 := by norm_num

/-
## Impact of Hypothetical Improvements
-/

/-- Any bound with exponent α strictly above the SV exponent reduces the
    remaining gap below 2/(d(d+2)).
    This formalizes the structure of the problem: partial improvements
    reduce the gap but do not close it. -/
theorem improvement_reduces_gap (d : ℕ) (hd : d ≥ 4) (α : ℝ)
    (hα : 2 * (↑d + 1) / (↑d * (↑d + 2)) < α) :
    2 / (↑d : ℝ) - α < 2 / (↑d * (↑d + 2)) := by
  linarith [gap_formula d hd]

/-- Matching the conjectured exponent exactly closes the gap to zero. -/
theorem exact_conjecture_closes_gap (d : ℕ) (hd : d ≥ 4) :
    2 / (↑d : ℝ) - 2 / ↑d = 0 := by ring

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

State of Erdős #1083 OQ-02:
- Erdős (1946): exponent 1/d
- Solymosi-Vu (2008): exponent 2(d+1)/(d(d+2)) = (d+1)/(d+2) · (2/d)
- Conjecture: exponent 2/d - o(1)
- Absolute gap: 2/(d(d+2)), with tight bounds 1/d² < gap < 2/d²
- Gap is strictly decreasing in d (monotone convergence to 0)
- Progress fraction: d/(d+2) of the [Erdős → conjecture] gap
- Relative gap: 1/(d+2) of the conjectured exponent

Axiom count: 5 (f, erdos_lower, grid_upper, solymosi_vu, conjecture)
Sorry count: 0
Proved: 23 theorems (gap analysis, progress fractions, near-optimality,
         quadratic bounds, factored structure)

Key insights:
1. SV = (d+1)/(d+2) · conjecture: the structural obstruction is the
   factor 1 - 1/(d+2) = d/(d+2), approaching 1 as d → ∞.
2. 1/d² < gap < 2/d²: the gap is exactly order 1/d², not smaller.
3. For each fixed d, the gap persists; no technique currently eliminates it.
-/

end Erdos1083OQ02
