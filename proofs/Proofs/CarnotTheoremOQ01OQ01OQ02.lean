import Mathlib
import Proofs.CarnotTheorem
import Proofs.CarnotTheoremOQ01OQ02

/-
# Carnot's Theorem — the sharp cosine-product bound and the lower range of the squared cosine sum

The sibling files pin down several extremal triangle trigonometric quantities:

* `CarnotTheoremOQ01OQ01` — the cosine **sum** range `(1, 3/2]` and Euler's
  inequality `r ≤ R/2`;
* `CarnotTheoremOQ01OQ02` — the **squared** cosine sum identity
  `cos²A + cos²B + cos²C = 1 - 2 cos A cos B cos C` and the acute/right/obtuse
  trichotomy against the value `1`.

What is missing there is the **sharp lower bound** of the squared cosine sum.
The trichotomy compares it to `1`, but the genuine extremum — the smallest
value `cos²A + cos²B + cos²C` can take over all triangles — is `3/4`, attained
at the equilateral triangle. Equivalently, through the sibling identity, the
**product** of the cosines is bounded sharply from above by `1/8`.

This file proves:

* `eight_cos_prod_identity` — for any reals with `A + B + C = π`,
  `1 - 8 cos A cos B cos C = (2 cos C - cos (A - B))² + sin (A - B)²`;
* `cos_prod_le_eighth`     — hence `cos A cos B cos C ≤ 1/8`;
* `cos_sq_sum_ge_three_quarters` — hence `cos²A + cos²B + cos²C ≥ 3/4`;
* `cos_prod_eq_eighth_iff` — equality `= 1/8` ⟺ the triangle is equilateral;
* `cos_sq_sum_eq_three_quarters_iff` — equality `= 3/4` ⟺ equilateral.

The whole argument rests on one sum-of-squares identity. Writing
`cos A cos B = ½(cos (A - B) - cos C)` (from `cos A cos B = ½(cos(A-B)+cos(A+B))`
and `cos(A+B) = -cos C` because `A + B = π - C`) turns

  `1 - 8 cos A cos B cos C = 1 - 4 cos (A - B) cos C + 4 cos²C`,

and completing the square against `cos²(A-B) + sin²(A-B) = 1` gives

  `= (2 cos C - cos (A - B))² + sin²(A - B) ≥ 0`.

The bound is therefore **sign-agnostic** — it holds for every real triple
summing to `π`, never splitting on acute/obtuse. Positivity of the angles is
needed only to identify the equality case as the equilateral triangle:
`sin(A-B) = 0` forces `A = B`, and `2 cos C = cos (A - B) = 1` forces
`C = π/3`.

**No axioms, no sorries.**
-/

open Real

namespace CarnotTheoremOQ01OQ01OQ02

/-- **Core sum-of-squares identity.**  For any reals with `A + B + C = π`,
`1 - 8 cos A cos B cos C = (2 cos C - cos (A - B))² + sin (A - B)²`.

This single identity drives every bound in this file. It is purely algebraic in
the three cosines once `A + B = π - C` is used to rewrite `cos (A + B)`; no
positivity of the angles is assumed. -/
theorem eight_cos_prod_identity (A B C : ℝ) (h : A + B + C = π) :
    1 - 8 * Real.cos A * Real.cos B * Real.cos C
      = (2 * Real.cos C - Real.cos (A - B)) ^ 2 + Real.sin (A - B) ^ 2 := by
  -- `cos (A + B) = -cos C` from the angle-sum constraint.
  have hAB : Real.cos (A + B) = - Real.cos C := by
    rw [show A + B = π - C by linarith, Real.cos_pi_sub]
  -- product-to-sum: `cos A cos B = ½ (cos (A - B) - cos C)`.
  have e1 := Real.cos_sub A B
  have e2 := Real.cos_add A B
  have hprod : Real.cos A * Real.cos B = (Real.cos (A - B) - Real.cos C) / 2 := by
    linarith [e1, e2, hAB]
  -- pythagorean identity for the `(A - B)` argument.
  have hpyth : Real.sin (A - B) ^ 2 = 1 - Real.cos (A - B) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (A - B); linarith
  rw [hpyth]
  linear_combination (-8 * Real.cos C) * hprod

/-- **Sharp cosine-product bound.**  For any reals with `A + B + C = π` (in
particular for every triangle), `cos A cos B cos C ≤ 1/8`.

Immediate from `eight_cos_prod_identity`: the right-hand side is a sum of two
squares, hence nonnegative, so `8 cos A cos B cos C ≤ 1`. The bound is sharp,
attained by the equilateral triangle (`cos_prod_eq_eighth_iff`). -/
theorem cos_prod_le_eighth (A B C : ℝ) (h : A + B + C = π) :
    Real.cos A * Real.cos B * Real.cos C ≤ 1 / 8 := by
  have hid := eight_cos_prod_identity A B C h
  nlinarith [hid, sq_nonneg (2 * Real.cos C - Real.cos (A - B)),
    sq_nonneg (Real.sin (A - B))]

/-- **Sharp lower bound on the squared cosine sum.**  For any reals with
`A + B + C = π`, `cos²A + cos²B + cos²C ≥ 3/4`.

The sibling identity `cos²A + cos²B + cos²C = 1 - 2 cos A cos B cos C` combined
with `cos A cos B cos C ≤ 1/8` gives the bound. It complements the sibling's
trichotomy against `1`: the *smallest* the squared sum can be is `3/4` (at the
equilateral triangle), while it ranges up towards `3` for degenerate triangles. -/
theorem cos_sq_sum_ge_three_quarters (A B C : ℝ) (h : A + B + C = π) :
    Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 ≥ 3 / 4 := by
  have hsq := CarnotTheoremOQ01OQ02.cos_sq_sum A B C h
  have hp := cos_prod_le_eighth A B C h
  linarith [hsq, hp]

/-- **Equality case for the product bound.**  For a triangle
(`A, B, C > 0`, `A + B + C = π`), `cos A cos B cos C = 1/8` if and only if the
triangle is equilateral (`A = B = C = π/3`).

Forward: equality forces the two squares in `eight_cos_prod_identity` to vanish,
i.e. `sin (A - B) = 0` and `2 cos C = cos (A - B)`. With `|A - B| < π` the first
gives `A = B`, so `cos (A - B) = 1` and `cos C = 1/2`; injectivity of cosine on
`[0, π]` gives `C = π/3`, and `A + B + C = π` then forces `A = B = π/3`.
Backward: `cos (π/3) = 1/2`. -/
theorem cos_prod_eq_eighth_iff (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A + B + C = π) :
    Real.cos A * Real.cos B * Real.cos C = 1 / 8 ↔
      A = π / 3 ∧ B = π / 3 ∧ C = π / 3 := by
  constructor
  · intro heq
    have hid := eight_cos_prod_identity A B C h
    -- the two squares sum to zero, hence each is zero
    have hsin0 : Real.sin (A - B) = 0 := by
      have hsq : Real.sin (A - B) ^ 2 = 0 := by
        nlinarith [hid, heq, sq_nonneg (2 * Real.cos C - Real.cos (A - B)),
          sq_nonneg (Real.sin (A - B))]
      exact pow_eq_zero_iff (by norm_num) |>.mp hsq
    have hcos0 : 2 * Real.cos C - Real.cos (A - B) = 0 := by
      have hsq : (2 * Real.cos C - Real.cos (A - B)) ^ 2 = 0 := by
        nlinarith [hid, heq, sq_nonneg (2 * Real.cos C - Real.cos (A - B)),
          sq_nonneg (Real.sin (A - B))]
      exact pow_eq_zero_iff (by norm_num) |>.mp hsq
    -- `sin (A - B) = 0` with `|A - B| < π` gives `A = B`
    have hABeq : A = B := by
      have hlt : -π < A - B := by linarith
      have hgt : A - B < π := by linarith
      have := (Real.sin_eq_zero_iff_of_lt_of_lt hlt hgt).mp hsin0
      linarith
    -- hence `cos (A - B) = 1` and `cos C = 1/2`
    have hcosC : Real.cos C = 1 / 2 := by
      have : Real.cos (A - B) = 1 := by
        rw [show A - B = 0 by linarith, Real.cos_zero]
      rw [this] at hcos0; linarith
    -- injectivity of cosine on `[0, π]` gives `C = π/3`
    have hCval : C = π / 3 := by
      have hmem1 : C ∈ Set.Icc 0 π := ⟨by linarith, by linarith⟩
      have hmem2 : π / 3 ∈ Set.Icc 0 π := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have heqcos : Real.cos C = Real.cos (π / 3) := by rw [hcosC, Real.cos_pi_div_three]
      exact Real.injOn_cos hmem1 hmem2 heqcos
    refine ⟨?_, ?_, hCval⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩
    rw [Real.cos_pi_div_three]; norm_num

/-- **Equality case for the squared-sum lower bound.**  For a triangle,
`cos²A + cos²B + cos²C = 3/4` if and only if the triangle is equilateral.

Transported from `cos_prod_eq_eighth_iff` through the sibling identity
`cos²A + cos²B + cos²C = 1 - 2 cos A cos B cos C`: the squared sum equals `3/4`
exactly when the product equals `1/8`. -/
theorem cos_sq_sum_eq_three_quarters_iff (A B C : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (h : A + B + C = π) :
    Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 = 3 / 4 ↔
      A = π / 3 ∧ B = π / 3 ∧ C = π / 3 := by
  have hsq := CarnotTheoremOQ01OQ02.cos_sq_sum A B C h
  rw [hsq]
  rw [show (1 : ℝ) - 2 * (Real.cos A * Real.cos B * Real.cos C) = 3 / 4
      ↔ Real.cos A * Real.cos B * Real.cos C = 1 / 8 by constructor <;> intro <;> linarith]
  exact cos_prod_eq_eighth_iff A B C hA hB hC h

end CarnotTheoremOQ01OQ01OQ02
