/-
Archimedes Pi Bounds: 223/71 < π < 22/7

Open Question (area-of-circle-oq-03-oq-02):
"Can Archimedes' specific bounds 3+10/71 < π < 3+1/7 (using 96-gons)
be verified computably in Lean 4?"

Answer: YES — both bounds follow from Mathlib's pi_gt_d4 (3.1415 < π)
and pi_lt_d4 (π < 3.1416), since 223/71 ≈ 3.14085 < 3.1415 and
3.1416 < 22/7 ≈ 3.14286. Fully verified, 0 axioms, 0 sorries.

References:
- Archimedes, "Measurement of a Circle" (c. 250 BCE)
- Dalzell (1944), Niven (1947): ∫₀¹ t⁴(1-t)⁴/(1+t²) dt = 22/7 - π
- Mathlib: Real.pi_gt_d4 (3.1415 < π), Real.pi_lt_d4 (π < 3.1416)
-/

import Mathlib

namespace AreaOfCircleOQ03OQ02

open Real

-- ============================================================
-- PART I: Pi Bounds (fully verified via Mathlib's pi_gt_d4/pi_lt_d4)
-- ============================================================

/-- π > 223/71 (Archimedes' lower bound, c. 250 BCE).
    223/71 ≈ 3.14084 < 3.1415 < π.
    Proved via Mathlib's pi_gt_d4 (3.1415 < π). -/
theorem archimedes_lower_bound : (223 : ℝ) / 71 < Real.pi := by
  have h1 : (223 : ℝ) / 71 < 3.1415 := by norm_num
  linarith [Real.pi_gt_d4]

/-- π < 22/7 (Archimedes' upper bound, c. 250 BCE).
    π < 3.1416 < 22/7 ≈ 3.14286.
    Proved via Mathlib's pi_lt_d4 (π < 3.1416). -/
theorem archimedes_upper_bound : Real.pi < (22 : ℝ) / 7 := by
  have h1 : (3.1416 : ℝ) < 22 / 7 := by norm_num
  linarith [Real.pi_lt_d4]

-- ============================================================
-- PART II: Derived Results (0 sorries)
-- ============================================================

/-- Archimedes' combined bounds -/
theorem archimedes_bounds : (223 : ℝ) / 71 < Real.pi ∧ Real.pi < (22 : ℝ) / 7 :=
  ⟨archimedes_lower_bound, archimedes_upper_bound⟩

/-- Traditional lower bound: 3 + 10/71 < π -/
theorem archimedes_lower_traditional : (3 : ℝ) + 10 / 71 < Real.pi := by
  have : (3 : ℝ) + 10 / 71 = 223 / 71 := by norm_num
  linarith [archimedes_lower_bound]

/-- Traditional upper bound: π < 3 + 1/7 -/
theorem archimedes_upper_traditional : Real.pi < (3 : ℝ) + 1 / 7 := by
  have : (3 : ℝ) + 1 / 7 = 22 / 7 := by norm_num
  linarith [archimedes_upper_bound]

/-- The gap between Archimedes' bounds: 22/7 − 223/71 = 1/497 -/
theorem archimedes_gap : (22 : ℝ) / 7 - 223 / 71 = 1 / 497 := by norm_num

/-- π is within 1/497 of both bounds -/
theorem archimedes_error_bound : Real.pi - 223 / 71 < 1 / 497 ∧
    (22 : ℝ) / 7 - Real.pi < 1 / 497 := by
  obtain ⟨hlower, hupper⟩ := archimedes_bounds
  constructor <;> linarith [archimedes_gap]

/-- 22/7 overestimates π by less than 3/1000 -/
theorem twentytwo_over_seven_error : (22 : ℝ) / 7 - Real.pi < 3 / 1000 := by
  have : (1 : ℝ) / 497 < 3 / 1000 := by norm_num
  linarith [archimedes_error_bound.2]

-- ============================================================
-- PART III: General Inscribed Polygon Bound (sorry-free)
-- ============================================================

/-- Inscribed polygon half-perimeter: n · sin(π/n) < π for n ≥ 1.
    The inscribed regular n-gon has perimeter 2n·r·sin(π/n),
    so perimeter/(2r) = n·sin(π/n) < π. -/
theorem inscribed_half_perimeter_lt_pi {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.sin (Real.pi / n) < Real.pi := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hpi_pos := Real.pi_pos
  have hu_pos : 0 < Real.pi / n := div_pos hpi_pos hn_pos
  have hsin_lt : Real.sin (Real.pi / n) < Real.pi / n := Real.sin_lt hu_pos
  calc (n : ℝ) * Real.sin (Real.pi / n)
      < n * (Real.pi / n) := mul_lt_mul_of_pos_left hsin_lt hn_pos
    _ = Real.pi := by field_simp

-- ============================================================
-- PART IV: Summary
-- ============================================================

/-- Summary: Archimedes' bounds fully verified (0 sorries, 0 axioms) -/
theorem archimedes_verified :
    ((223 : ℝ) / 71 < Real.pi ∧ Real.pi < 22 / 7) ∧
    ((22 : ℝ) / 7 - 223 / 71 = 1 / 497) ∧
    (∀ n : ℕ, 1 ≤ n → (n : ℝ) * Real.sin (Real.pi / n) < Real.pi) :=
  ⟨archimedes_bounds, archimedes_gap, fun _ hn => inscribed_half_perimeter_lt_pi hn⟩

end AreaOfCircleOQ03OQ02
