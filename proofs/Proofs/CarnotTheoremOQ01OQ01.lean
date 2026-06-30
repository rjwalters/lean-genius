import Mathlib
import Proofs.CarnotTheorem

/-
# Carnot's Theorem — the cosine-sum range and Euler's inequality

The parent file `CarnotTheorem.lean` proves the angle form of Carnot's theorem,

  `cos A + cos B + cos C = 1 + 4 sin(A/2) sin(B/2) sin(C/2)`,

valid for any reals with `A + B + C = π`. Through the circumradius/inradius
identity `r / R = 4 sin(A/2) sin(B/2) sin(C/2)` this reads
`cos A + cos B + cos C = 1 + r / R`, the trigonometric heart of Carnot's
theorem obtained by summing the signed circumcenter-to-side distances
`R cos A + R cos B + R cos C = R + r`.

This file pins down the **range** of that cosine sum for an actual triangle
(`A, B, C > 0`, `A + B + C = π`) and extracts the classical consequences:

* `cos_sum_le`        — `cos A + cos B + cos C ≤ 3/2` (upper bound, attained);
* `one_lt_cos_sum`    — `1 < cos A + cos B + cos C` (strict lower bound);
* `cos_sum_eq_three_halves_iff` — equality `= 3/2` ⟺ the triangle is equilateral;
* `euler_inequality`  — `4 sin(A/2) sin(B/2) sin(C/2) ≤ 1/2`, i.e. `r ≤ R/2`.

The whole range `(1, 3/2]` of the cosine sum corresponds, through the parent
identity, to the geometric range `(0, 1/2]` of `r / R`; Euler's inequality
`r ≤ R/2` is the upper endpoint restated.

The upper bound rests on the single algebraic decomposition

  `cos A + cos B + cos C
     = 3/2 - 2 (sin(C/2) - 1/2)² - 2 sin(C/2) (1 - cos((A-B)/2))`,

obtained from the sum-to-product form `cos A + cos B = 2 sin(C/2) cos((A-B)/2)`
(using `(A+B)/2 = π/2 - C/2`) together with `cos C = 1 - 2 sin²(C/2)`. Both
subtracted terms are nonnegative, and they vanish simultaneously exactly when
`sin(C/2) = 1/2` and `cos((A-B)/2) = 1`, i.e. `C = π/3` and `A = B`. The
argument is sign-agnostic — it never splits on acute/obtuse — because it uses
only `A, B, C > 0` and `A + B + C = π`.

**No axioms, no sorries.**
-/

open Real

namespace CarnotTheoremOQ01OQ01

/-- Double-angle in the `1 - 2 sin²` form (mirrors the parent file). -/
private theorem cos_two_mul_sin (x : ℝ) : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
  rw [Real.cos_two_mul']
  linear_combination Real.cos_sq_add_sin_sq x

/-- The key sum-to-product decomposition: for `A + B + C = π`,
`cos A + cos B + cos C = 1 + 2 sin(C/2) cos((A-B)/2) - 2 sin²(C/2)`. -/
private theorem cos_sum_decomp (A B C : ℝ) (h : A + B + C = π) :
    Real.cos A + Real.cos B + Real.cos C
      = 1 + 2 * Real.sin (C / 2) * Real.cos ((A - B) / 2) - 2 * Real.sin (C / 2) ^ 2 := by
  have hAB : Real.cos A + Real.cos B
      = 2 * Real.sin (C / 2) * Real.cos ((A - B) / 2) := by
    rw [Real.cos_add_cos]
    have hmid : (A + B) / 2 = π / 2 - C / 2 := by linarith
    rw [hmid, Real.cos_pi_div_two_sub]
  have hcC : Real.cos C = 1 - 2 * Real.sin (C / 2) ^ 2 := by
    have h2 := cos_two_mul_sin (C / 2); rwa [show 2 * (C / 2) = C by ring] at h2
  rw [hcC]
  linear_combination hAB

/-- **Upper bound on the triangle cosine sum.**  For a triangle
(`A, B, C > 0`, `A + B + C = π`), `cos A + cos B + cos C ≤ 3/2`.

This is the analytic form of Euler's inequality `r ≤ R/2`; the bound is sharp,
attained by the equilateral triangle (`cos_sum_eq_three_halves_iff`). -/
theorem cos_sum_le (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A + B + C = π) : Real.cos A + Real.cos B + Real.cos C ≤ 3 / 2 := by
  have hdecomp := cos_sum_decomp A B C h
  have hs : 0 ≤ Real.sin (C / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hd : Real.cos ((A - B) / 2) ≤ 1 := Real.cos_le_one _
  -- 3/2 - sum = 2 (s - 1/2)² + 2 s (1 - d) ≥ 0
  nlinarith [hdecomp, sq_nonneg (Real.sin (C / 2) - 1 / 2),
    mul_nonneg hs (by linarith : (0 : ℝ) ≤ 1 - Real.cos ((A - B) / 2))]

/-- **Strict lower bound on the triangle cosine sum.**  For a triangle,
`1 < cos A + cos B + cos C`.

Via the parent identity the sum is `1 + 4 sin(A/2) sin(B/2) sin(C/2)`, and each
half-angle sine is positive because `A/2, B/2, C/2 ∈ (0, π/2)`. -/
theorem one_lt_cos_sum (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A + B + C = π) : 1 < Real.cos A + Real.cos B + Real.cos C := by
  rw [CarnotTheorem.carnot_cos_sum A B C h]
  have sA : 0 < Real.sin (A / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have sB : 0 < Real.sin (B / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have sC : 0 < Real.sin (C / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  nlinarith [mul_pos (mul_pos sA sB) sC]

/-- **Euler's inequality** (analytic form).  For a triangle,
`4 sin(A/2) sin(B/2) sin(C/2) ≤ 1/2`.

Geometrically `r / R = 4 sin(A/2) sin(B/2) sin(C/2)`, so this is `r ≤ R/2`. It
is the upper bound `cos_sum_le` transported through the parent angle identity. -/
theorem euler_inequality (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A + B + C = π) :
    4 * Real.sin (A / 2) * Real.sin (B / 2) * Real.sin (C / 2) ≤ 1 / 2 := by
  have hid := CarnotTheorem.carnot_cos_sum A B C h
  have hle := cos_sum_le A B C hA hB hC h
  linarith [hid, hle]

/-- **Equality case.**  For a triangle, `cos A + cos B + cos C = 3/2` holds
if and only if the triangle is equilateral (`A = B = C = π/3`).

Forward: the slack `3/2 - sum = 2 (sin(C/2) - 1/2)² + 2 sin(C/2)(1 - cos((A-B)/2))`
is a sum of two nonnegative terms, so equality forces both to vanish:
`sin(C/2) = 1/2` (hence `C = π/3`) and `cos((A-B)/2) = 1` (hence `A = B`), and
with `A + B + C = π` this gives `A = B = π/3`. Backward: `cos(π/3) = 1/2`. -/
theorem cos_sum_eq_three_halves_iff (A B C : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (h : A + B + C = π) :
    Real.cos A + Real.cos B + Real.cos C = 3 / 2 ↔ A = π / 3 ∧ B = π / 3 ∧ C = π / 3 := by
  constructor
  · intro heq
    have hdecomp := cos_sum_decomp A B C h
    have hs : 0 ≤ Real.sin (C / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hd : Real.cos ((A - B) / 2) ≤ 1 := Real.cos_le_one _
    -- both slack terms are zero
    have hsq : (Real.sin (C / 2) - 1 / 2) ^ 2 = 0 := by
      nlinarith [hdecomp, sq_nonneg (Real.sin (C / 2) - 1 / 2),
        mul_nonneg hs (by linarith : (0 : ℝ) ≤ 1 - Real.cos ((A - B) / 2))]
    have hprod : Real.sin (C / 2) * (1 - Real.cos ((A - B) / 2)) = 0 := by
      nlinarith [hdecomp, sq_nonneg (Real.sin (C / 2) - 1 / 2),
        mul_nonneg hs (by linarith : (0 : ℝ) ≤ 1 - Real.cos ((A - B) / 2))]
    -- sin(C/2) = 1/2
    have hsin : Real.sin (C / 2) = 1 / 2 := by
      have hz : Real.sin (C / 2) - 1 / 2 = 0 := sq_eq_zero_iff.mp hsq
      linarith
    -- C/2 = π/6, hence C = π/3
    have hCval : C = π / 3 := by
      have hmem1 : C / 2 ∈ Set.Icc (-(π / 2)) (π / 2) :=
        ⟨by linarith, by linarith⟩
      have hmem2 : π / 6 ∈ Set.Icc (-(π / 2)) (π / 2) :=
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have heqsin : Real.sin (C / 2) = Real.sin (π / 6) := by
        rw [hsin, Real.sin_pi_div_six]
      have := Real.injOn_sin hmem1 hmem2 heqsin
      linarith
    -- cos((A-B)/2) = 1 since sin(C/2) = 1/2 ≠ 0
    have hcos1 : Real.cos ((A - B) / 2) = 1 := by
      rw [hsin] at hprod
      have : (1 : ℝ) - Real.cos ((A - B) / 2) = 0 := by
        rcases mul_eq_zero.mp hprod with h1 | h2
        · norm_num at h1
        · exact h2
      linarith
    -- (A-B)/2 = 0, hence A = B
    have hAB : A = B := by
      have hrange1 : -(2 * π) < (A - B) / 2 := by linarith [Real.pi_pos]
      have hrange2 : (A - B) / 2 < 2 * π := by linarith [Real.pi_pos]
      have := (Real.cos_eq_one_iff_of_lt_of_lt hrange1 hrange2).mp hcos1
      linarith
    refine ⟨?_, ?_, hCval⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩
    rw [Real.cos_pi_div_three]; norm_num

end CarnotTheoremOQ01OQ01
