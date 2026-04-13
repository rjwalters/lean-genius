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
Proved: 5 theorems (gap analysis, exponent comparison)

The gap 2/(d(d+2)) shrinks as d grows but remains polynomial for
each fixed d. No known approach eliminates it completely.
-/

end Erdos1083OQ02
