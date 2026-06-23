import Mathlib
import Proofs.CarnotTheorem

/-
# Carnot's Theorem — the companion sine sum and the sharp perimeter bound

The parent file `CarnotTheorem.lean` proves the **cosine** form of Carnot's
theorem for the angles of a triangle (any reals with `A + B + C = π`),

  `cos A + cos B + cos C = 1 + 4 sin(A/2) sin(B/2) sin(C/2)`,

the analytic core of `cos A + cos B + cos C = 1 + r/R`. This file develops the
**dual sine identity**

  `sin A + sin B + sin C = 4 cos(A/2) cos(B/2) cos(C/2)`,

valid for any reals with `A + B + C = π`. For a triangle inscribed in a circle of
radius `R` the law of sines gives `a = 2R sin A`, etc., so

  `a + b + c = 2R (sin A + sin B + sin C)`,

i.e. the sine sum is the **perimeter measured in units of the circumdiameter**.
The product form `4 cos(A/2) cos(B/2) cos(C/2)` is its half-angle factorisation
(it equals `s/R`, with `s` the semiperimeter).

Two consequences are proved:

* **Positivity.** For a genuine triangle (`A, B, C > 0`) every angle lies in
  `(0, π)`, so each sine is positive and the sum is positive.

* **Sharp maximum.** Because `sin` is concave on `[0, π]`, Jensen's inequality at
  the barycentre `(A + B + C)/3 = π/3` gives

    `sin A + sin B + sin C ≤ 3 sin(π/3) = 3√3 / 2`,

  with equality for the equilateral triangle `A = B = C = π/3`. Equivalently, among
  all triangles inscribed in a fixed circle the equilateral one has the largest
  perimeter.

Everything is built on Mathlib's FTC-free trigonometric primitives and the
concavity lemma `strictConcaveOn_sin_Icc`; nothing here re-uses the parent's
cosine identity, so the sine identity is proved from scratch in the same
half-angle style.

**No axioms, no sorries.**
-/

open Real

namespace CarnotTheoremOQ01OQ03

/-- **Companion sine identity.**  For any reals `A, B, C` with `A + B + C = π`,
`sin A + sin B + sin C = 4 cos(A/2) cos(B/2) cos(C/2)`.

This is the dual of the parent's `carnot_cos_sum`. Writing each full-angle sine as
`2 sin(·/2) cos(·/2)` and expressing the half-angle of `C` through those of `A`
and `B` (using `C/2 = π/2 - (A/2 + B/2)`), the claim reduces to a `ring` identity
modulo the Pythagorean relations for `A/2` and `B/2`. -/
theorem carnot_sin_sum (A B C : ℝ) (h : A + B + C = π) :
    Real.sin A + Real.sin B + Real.sin C
      = 4 * Real.cos (A / 2) * Real.cos (B / 2) * Real.cos (C / 2) := by
  -- Express the half-angle of `C` through those of `A` and `B`.
  have hsC : Real.sin (C / 2)
      = Real.cos (A / 2) * Real.cos (B / 2) - Real.sin (A / 2) * Real.sin (B / 2) := by
    have hch : C / 2 = π / 2 - (A / 2 + B / 2) := by linarith
    rw [hch, Real.sin_pi_div_two_sub, Real.cos_add]
  have hcC : Real.cos (C / 2)
      = Real.sin (A / 2) * Real.cos (B / 2) + Real.cos (A / 2) * Real.sin (B / 2) := by
    have hch : C / 2 = π / 2 - (A / 2 + B / 2) := by linarith
    rw [hch, Real.cos_pi_div_two_sub, Real.sin_add]
  -- Double-angle each full-angle sine.
  have hsa : Real.sin A = 2 * Real.sin (A / 2) * Real.cos (A / 2) := by
    have hx := Real.sin_two_mul (A / 2); rwa [show 2 * (A / 2) = A by ring] at hx
  have hsb : Real.sin B = 2 * Real.sin (B / 2) * Real.cos (B / 2) := by
    have hx := Real.sin_two_mul (B / 2); rwa [show 2 * (B / 2) = B by ring] at hx
  have hsc : Real.sin C = 2 * Real.sin (C / 2) * Real.cos (C / 2) := by
    have hx := Real.sin_two_mul (C / 2); rwa [show 2 * (C / 2) = C by ring] at hx
  rw [hsa, hsb, hsc, hsC, hcC]
  linear_combination (-2 * Real.sin (A / 2) * Real.cos (A / 2)) * Real.sin_sq_add_cos_sq (B / 2)
    + (-2 * Real.sin (B / 2) * Real.cos (B / 2)) * Real.sin_sq_add_cos_sq (A / 2)

/-- **Positivity of the sine sum.**  For a genuine triangle (`A, B, C > 0`,
`A + B + C = π`), `0 < sin A + sin B + sin C`.

Each angle lies in `(0, π)` (e.g. `A = π - B - C < π` since `B, C > 0`), so each
sine is strictly positive. -/
theorem sin_sum_pos (A B C : ℝ)
    (hA0 : 0 < A) (hB0 : 0 < B) (hC0 : 0 < C) (h : A + B + C = π) :
    0 < Real.sin A + Real.sin B + Real.sin C := by
  have pA : 0 < Real.sin A := Real.sin_pos_of_pos_of_lt_pi hA0 (by linarith)
  have pB : 0 < Real.sin B := Real.sin_pos_of_pos_of_lt_pi hB0 (by linarith)
  have pC : 0 < Real.sin C := Real.sin_pos_of_pos_of_lt_pi hC0 (by linarith)
  linarith

/-- **Sharp maximum of the sine sum.**  For any reals with `A + B + C = π` and
all of `A, B, C ∈ [0, π]`,
`sin A + sin B + sin C ≤ 3√3 / 2`.

`sin` is concave on `[0, π]` (`strictConcaveOn_sin_Icc`). Applying the two-point
concavity inequality first to the midpoint `M = (B + C)/2` of `B, C` and then to
`A` (weight `1/3`) against `M` (weight `2/3`) lands at the barycentre
`(1/3)A + (2/3)M = (A + B + C)/3 = π/3`, giving
`(sin A + sin B + sin C)/3 ≤ sin(π/3) = √3/2`.
The hypotheses `A, B, C ∈ [0, π]` hold automatically for the angles of a triangle.
The bound is attained at the equilateral triangle (see
`sin_sum_eq_at_equilateral`). -/
theorem sin_sum_le (A B C : ℝ)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (h : A + B + C = π) :
    Real.sin A + Real.sin B + Real.sin C ≤ 3 * Real.sqrt 3 / 2 := by
  have hconc : ConcaveOn ℝ (Set.Icc 0 π) Real.sin := strictConcaveOn_sin_Icc.concaveOn
  have memA : A ∈ Set.Icc (0 : ℝ) π := ⟨hA0, by linarith⟩
  have memB : B ∈ Set.Icc (0 : ℝ) π := ⟨hB0, by linarith⟩
  have memC : C ∈ Set.Icc (0 : ℝ) π := ⟨hC0, by linarith⟩
  set M : ℝ := (B + C) / 2 with hM
  have memM : M ∈ Set.Icc (0 : ℝ) π := ⟨by rw [hM]; linarith, by rw [hM]; linarith⟩
  -- Two-point concavity at the midpoint of `B` and `C`.
  have step1 := hconc.2 memB memC (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at step1
  have e1 : (1 / 2 : ℝ) * B + 1 / 2 * C = M := by rw [hM]; ring
  rw [e1] at step1
  -- Two-point concavity combining `A` (weight 1/3) with `M` (weight 2/3).
  have step2 := hconc.2 memA memM (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (1 / 3 : ℝ) + 2 / 3 = 1)
  simp only [smul_eq_mul] at step2
  have e2 : (1 / 3 : ℝ) * A + 2 / 3 * M = π / 3 := by rw [hM]; linarith
  rw [e2, Real.sin_pi_div_three] at step2
  -- `3·step2 + 2·step1` cancels `sin M` and yields the bound.
  linarith [step1, step2]

/-- **Sharpness witness.**  The equilateral triangle `A = B = C = π/3` attains the
maximum: `sin(π/3) + sin(π/3) + sin(π/3) = 3√3 / 2`. Together with `sin_sum_le`
this shows the bound `3√3 / 2` is the exact supremum of the triangle sine sum. -/
theorem sin_sum_eq_at_equilateral :
    Real.sin (π / 3) + Real.sin (π / 3) + Real.sin (π / 3) = 3 * Real.sqrt 3 / 2 := by
  rw [Real.sin_pi_div_three]; ring

end CarnotTheoremOQ01OQ03
