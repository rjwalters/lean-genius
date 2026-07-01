/-
  Acute–Right–Obtuse Trichotomy from the Law of Cosines (Euclid II.12 / II.13)

  The Law of Cosines `c² = a² + b² - 2ab·cos C` turns the classification of a
  triangle's angle into a purely algebraic comparison of the squared sides:

      C < π/2  ⟺  c² < a² + b²    (acute — Euclid II.13)
      C = π/2  ⟺  c² = a² + b²    (right  — Pythagoras)
      C > π/2  ⟺  c² > a² + b²    (obtuse — Euclid II.12)

  This is the converse-and-refinement of the Pythagorean theorem that Euclid
  states as propositions II.12 and II.13: the sign of `a² + b² - c²` records
  whether the angle opposite `c` is acute, right, or obtuse.

  The engine is the sign of `cos C` on `[0, π]` (positive below π/2, zero at π/2,
  negative above), multiplied by the positive quantity `2ab`; the Law of Cosines
  hypothesis then transfers that sign to `a² + b² - c²`.

  Key results:
  - `angle_acute_iff`, `angle_right_iff`, `angle_obtuse_iff`: the three
    equivalences.

  Euclid, *Elements* Book II, Propositions 12–13 (c. 300 BCE)
-/
import Mathlib

namespace LawOfCosinesOQ09

open Real

variable {a b c C : ℝ}

-- ============================================================
-- Sign of cos C against π/2 on [0, π]
-- ============================================================

/-- On `[0, π]`, `cos C > 0` exactly when `C < π/2`. -/
private theorem cos_pos_iff_lt (hC0 : 0 ≤ C) (hCpi : C ≤ π) :
    0 < Real.cos C ↔ C < π / 2 := by
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    have : Real.cos C ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hle (by linarith [Real.pi_pos])
    linarith
  · intro h
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h⟩

/-- On `[0, π]`, `cos C = 0` exactly when `C = π/2`. -/
private theorem cos_eq_zero_iff_eq (hC0 : 0 ≤ C) (hCpi : C ≤ π) :
    Real.cos C = 0 ↔ C = π / 2 := by
  constructor
  · intro h
    refine Real.strictAntiOn_cos.injOn ⟨hC0, hCpi⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ ?_
    rw [h, Real.cos_pi_div_two]
  · intro h; rw [h, Real.cos_pi_div_two]

/-- On `[0, π]`, `cos C < 0` exactly when `C > π/2`. -/
private theorem cos_neg_iff_gt (hC0 : 0 ≤ C) (hCpi : C ≤ π) :
    Real.cos C < 0 ↔ π / 2 < C := by
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    have : 0 ≤ Real.cos C := by
      rcases eq_or_lt_of_le hle with heq | hlt
      · simp [heq, Real.cos_pi_div_two]
      · exact le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩)
    linarith
  · intro h
    exact Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith [Real.pi_pos])

-- ============================================================
-- The trichotomy
-- ============================================================

/-- **Acute angle (Euclid II.13).** With `a, b > 0`, `C ∈ [0, π]`, and the Law of
    Cosines `c² = a² + b² - 2ab·cos C`, the angle `C` is acute iff `c² < a² + b²`. -/
theorem angle_acute_iff (ha : 0 < a) (hb : 0 < b) (hC0 : 0 ≤ C) (hCpi : C ≤ π)
    (hlc : c ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * Real.cos C) :
    C < π / 2 ↔ c ^ 2 < a ^ 2 + b ^ 2 := by
  rw [← cos_pos_iff_lt hC0 hCpi]
  have h2ab : (0 : ℝ) < 2 * a * b := by positivity
  constructor
  · intro h; linarith [mul_pos h2ab h, hlc]
  · intro h
    have hpos : 0 < 2 * a * b * Real.cos C := by linarith [hlc]
    nlinarith [hpos, h2ab]

/-- **Right angle (Pythagoras).** Under the same hypotheses, `C` is a right angle
    iff `c² = a² + b²`. -/
theorem angle_right_iff (ha : 0 < a) (hb : 0 < b) (hC0 : 0 ≤ C) (hCpi : C ≤ π)
    (hlc : c ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * Real.cos C) :
    C = π / 2 ↔ c ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← cos_eq_zero_iff_eq hC0 hCpi]
  have h2ab : (0 : ℝ) < 2 * a * b := by positivity
  constructor
  · intro h
    have hz : 2 * a * b * Real.cos C = 0 := by rw [h]; ring
    linarith [hlc, hz]
  · intro h
    have hz : 2 * a * b * Real.cos C = 0 := by linarith [hlc]
    rcases mul_eq_zero.mp hz with h2 | hcos
    · exact absurd h2 (ne_of_gt h2ab)
    · exact hcos

/-- **Obtuse angle (Euclid II.12).** Under the same hypotheses, `C` is obtuse iff
    `c² > a² + b²`. -/
theorem angle_obtuse_iff (ha : 0 < a) (hb : 0 < b) (hC0 : 0 ≤ C) (hCpi : C ≤ π)
    (hlc : c ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * Real.cos C) :
    π / 2 < C ↔ a ^ 2 + b ^ 2 < c ^ 2 := by
  rw [← cos_neg_iff_gt hC0 hCpi]
  have h2ab : (0 : ℝ) < 2 * a * b := by positivity
  constructor
  · intro h
    have hneg : 2 * a * b * Real.cos C < 0 := mul_neg_of_pos_of_neg h2ab h
    linarith [hlc, hneg]
  · intro h
    have hneg : 2 * a * b * Real.cos C < 0 := by linarith [hlc]
    nlinarith [hneg, h2ab]

end LawOfCosinesOQ09
