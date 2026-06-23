import Mathlib
import Proofs.CarnotTheorem

/-
# The Exact Range of the Cosine Sum of a Triangle (Euler's Inequality)

## Open Question OQ-01-OQ-01

The parent file (Carnot, angle form) proves the identity

  cos A + cos B + cos C = 1 + 4 sin(A/2) sin(B/2) sin(C/2)        (for A + B + C = π),

equivalently `cos A + cos B + cos C = 1 + r/R`.  This raises the sharp-boundary
question: as the triangle varies, what is the *exact range* of the quantity
`cos A + cos B + cos C`?

We pin it down.  For every genuine triangle (`A, B, C > 0`, `A + B + C = π`),

  1 < cos A + cos B + cos C ≤ 3/2,

the upper bound being attained **iff** the triangle is equilateral
(`A = B = C = π/3`), while `1` is the (never attained) degenerate infimum.
Through the parent identity the upper bound is exactly **Euler's inequality**
`r ≤ R/2`, here in the form `4 sin(A/2) sin(B/2) sin(C/2) ≤ 1/2`.

## Proof of the upper bound

Sum-to-product on two cosines, using `(A+B)/2 = π/2 − C/2`:

  cos A + cos B = 2 cos((A+B)/2) cos((A−B)/2) = 2 sin(C/2) cos((A−B)/2),

so with `cos C = 1 − 2 sin²(C/2)` and `t := sin(C/2) ≥ 0`,

  cos A + cos B + cos C = 2 t · cos((A−B)/2) + 1 − 2 t²
                        ≤ 2 t + 1 − 2 t²              (cos((A−B)/2) ≤ 1)
                        = 3/2 − 2 (t − 1/2)²  ≤  3/2.

Equality forces both slacks to vanish: `t = 1/2` (so `C = π/3`) and
`cos((A−B)/2) = 1` (so `A = B`), whence `A = B = C = π/3`.  The lower bound is
immediate from the parent identity, since each half-angle sine is positive.

## Results

1. `cos_sum_le` — the sharp upper bound `cos A + cos B + cos C ≤ 3/2`.
2. `one_lt_cos_sum` — the strict lower bound `1 < cos A + cos B + cos C`.
3. `cos_sum_eq_three_halves_iff` — equality `= 3/2` ⟺ `A = B = C = π/3`.
4. `euler_inequality` — `4 sin(A/2) sin(B/2) sin(C/2) ≤ 1/2`, i.e. `r ≤ R/2`.

## Axioms: 0 | Sorries: 0
-/

open Real

namespace CarnotTheoremOQ01OQ01

/-- **Sharp upper bound.**  For a triangle (`A, B, C > 0`, `A + B + C = π`),
`cos A + cos B + cos C ≤ 3/2`.  Sum-to-product turns two of the cosines into
`2 sin(C/2) cos((A−B)/2)`; bounding `cos((A−B)/2) ≤ 1` and completing the square
in `sin(C/2)` lands on `3/2`. -/
theorem cos_sum_le (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A + B + C = π) :
    Real.cos A + Real.cos B + Real.cos C ≤ 3 / 2 := by
  have hAB2 : (A + B) / 2 = π / 2 - C / 2 := by linarith
  have hsum : Real.cos A + Real.cos B
      = 2 * Real.sin (C / 2) * Real.cos ((A - B) / 2) := by
    rw [Real.cos_add_cos, hAB2, Real.cos_pi_div_two_sub]
  have hcosC : Real.cos C = 1 - 2 * Real.sin (C / 2) ^ 2 := by
    have e := Real.cos_two_mul (C / 2)
    rw [show 2 * (C / 2) = C by ring] at e
    have p := Real.sin_sq_add_cos_sq (C / 2)
    linarith [e, p]
  have hCltpi : C < π := by linarith
  have hsinC2nonneg : 0 ≤ Real.sin (C / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hcosle : Real.cos ((A - B) / 2) ≤ 1 := Real.cos_le_one _
  have hbound : 2 * Real.sin (C / 2) * Real.cos ((A - B) / 2)
      ≤ 2 * Real.sin (C / 2) := by
    nlinarith [hsinC2nonneg, hcosle]
  nlinarith [hsum, hcosC, hbound, sq_nonneg (Real.sin (C / 2) - 1 / 2)]

/-- **Strict lower bound.**  For a triangle, `1 < cos A + cos B + cos C`.
By the parent identity the excess over `1` equals `4 sin(A/2) sin(B/2) sin(C/2)`,
a product of three positive half-angle sines. -/
theorem one_lt_cos_sum (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A + B + C = π) :
    1 < Real.cos A + Real.cos B + Real.cos C := by
  rw [CarnotTheorem.carnot_cos_sum A B C h]
  have pA : 0 < Real.sin (A / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have pB : 0 < Real.sin (B / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have pC : 0 < Real.sin (C / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  nlinarith [mul_pos (mul_pos pA pB) pC]

/-- **Equality case.**  The upper bound is sharp exactly at the equilateral
triangle: `cos A + cos B + cos C = 3/2 ↔ A = B = C = π/3`.  Forward, the exact
slack decomposition
`3/2 − (cos A+cos B+cos C) = 2 sin(C/2)(1−cos((A−B)/2)) + 2(sin(C/2)−1/2)²`
forces `sin(C/2) = 1/2` (so `C = π/3`) and `cos((A−B)/2) = 1` (so `A = B`). -/
theorem cos_sum_eq_three_halves_iff (A B C : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (h : A + B + C = π) :
    Real.cos A + Real.cos B + Real.cos C = 3 / 2
      ↔ A = π / 3 ∧ B = π / 3 ∧ C = π / 3 := by
  constructor
  · intro heq
    have hAB2 : (A + B) / 2 = π / 2 - C / 2 := by linarith
    have hsum : Real.cos A + Real.cos B
        = 2 * Real.sin (C / 2) * Real.cos ((A - B) / 2) := by
      rw [Real.cos_add_cos, hAB2, Real.cos_pi_div_two_sub]
    have hcosC : Real.cos C = 1 - 2 * Real.sin (C / 2) ^ 2 := by
      have e := Real.cos_two_mul (C / 2)
      rw [show 2 * (C / 2) = C by ring] at e
      have p := Real.sin_sq_add_cos_sq (C / 2)
      linarith [e, p]
    have hCltpi : C < π := by linarith
    have hsinC2nonneg : 0 ≤ Real.sin (C / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
    have hcosle : Real.cos ((A - B) / 2) ≤ 1 := Real.cos_le_one _
    -- The exact value of the cosine sum in terms of `t = sin(C/2)`.
    have hcombine : 2 * Real.sin (C / 2) * Real.cos ((A - B) / 2)
        + (1 - 2 * Real.sin (C / 2) ^ 2) = 3 / 2 := by
      rw [← hsum, ← hcosC]; linarith [heq]
    -- Slack as a sum of two manifestly nonnegative terms, equal to zero.
    have hzero : 2 * Real.sin (C / 2) * (1 - Real.cos ((A - B) / 2))
        + 2 * (Real.sin (C / 2) - 1 / 2) ^ 2 = 0 := by
      linear_combination -hcombine
    have hterm1 : 0 ≤ 2 * Real.sin (C / 2) * (1 - Real.cos ((A - B) / 2)) := by
      nlinarith [hsinC2nonneg, hcosle]
    have hz2 : (Real.sin (C / 2) - 1 / 2) ^ 2 = 0 := by
      nlinarith [hzero, hterm1, sq_nonneg (Real.sin (C / 2) - 1 / 2)]
    have hsm0 : Real.sin (C / 2) - 1 / 2 = 0 := by
      have := sq_eq_zero_iff.mp hz2
      linarith [this]
    have hsinhalf : Real.sin (C / 2) = 1 / 2 := by linarith [hsm0]
    -- `C = π/3` from `sin(C/2) = 1/2` and `0 < C/2 < π/2`.
    have hmem1 : C / 2 ∈ Set.Icc (-(π / 2)) (π / 2) :=
      Set.mem_Icc.mpr ⟨by linarith [Real.pi_pos], by linarith⟩
    have hmem2 : π / 6 ∈ Set.Icc (-(π / 2)) (π / 2) :=
      Set.mem_Icc.mpr ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have heqsin : Real.sin (C / 2) = Real.sin (π / 6) := by
      rw [hsinhalf, Real.sin_pi_div_six]
    have hCval : C / 2 = π / 6 := Real.injOn_sin hmem1 hmem2 heqsin
    have hCeq : C = π / 3 := by linarith [hCval]
    -- `A = B` from `cos((A−B)/2) = 1`.
    have hh : 2 * Real.sin (C / 2) * (1 - Real.cos ((A - B) / 2)) = 0 := by
      nlinarith [hzero, hz2]
    rw [hsinhalf] at hh
    have hcos1 : Real.cos ((A - B) / 2) = 1 := by nlinarith [hh]
    have hx0 : (A - B) / 2 = 0 :=
      (Real.cos_eq_one_iff_of_lt_of_lt
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).mp hcos1
    have hABeq : A = B := by linarith [hx0]
    refine ⟨by linarith [hABeq, hCeq], by linarith [hABeq, hCeq], hCeq⟩
  · rintro ⟨hA', hB', hC'⟩
    rw [hA', hB', hC', Real.cos_pi_div_three]
    norm_num

/-- **Euler's inequality (analytic form).**  For a triangle,
`4 sin(A/2) sin(B/2) sin(C/2) ≤ 1/2`.  Equivalently `r/R ≤ 1/2`, i.e. `r ≤ R/2`:
the inradius is at most half the circumradius.  Immediate from `cos_sum_le`
through the parent identity. -/
theorem euler_inequality (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A + B + C = π) :
    4 * Real.sin (A / 2) * Real.sin (B / 2) * Real.sin (C / 2) ≤ 1 / 2 := by
  have hle := cos_sum_le A B C hA hB hC h
  rw [CarnotTheorem.carnot_cos_sum A B C h] at hle
  linarith [hle]

/-- Sharpness check: the equilateral triangle attains the upper bound `3/2`. -/
example : Real.cos (π / 3) + Real.cos (π / 3) + Real.cos (π / 3) = 3 / 2 := by
  rw [Real.cos_pi_div_three]; norm_num

end CarnotTheoremOQ01OQ01
