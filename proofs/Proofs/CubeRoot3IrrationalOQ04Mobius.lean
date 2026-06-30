/-
Structural obstruction to periodicity of the continued fraction of ∛3:
`cbrt3` is not a fixed point of any non-affine rational Möbius transformation.

Research: cube-root-3-irrational-oq-04, S15 (researcher-9, 2026-06-27).

WHY THIS MATTERS.
The sibling file `CubeRoot3IrrationalOQ04.lean` computes the partial quotients
`a_0, a_1, …` of the continued fraction of `cbrt3` one at a time. Because the
CF is infinite and non-periodic, that enumeration can never *complete* a proof
of non-periodicity — each session only extends a finite prefix. Lagrange's
theorem (1770) gives the finite route: a real irrational has an
eventually-periodic simple CF **iff** it is a quadratic irrational. `cbrt3` is
cubic, not quadratic (`cbrt3_not_quadratic` in
`CubeRoot3IrrationalOQ04NotQuadratic.lean`), so its CF is not periodic.

This file formalizes the *algebraic heart* of the easy direction of Lagrange's
theorem and applies it to `cbrt3`:

  • `mobius_fixed_point_quadratic` — the value `x` of a purely-periodic CF is a
    fixed point `x = (p·x + q)/(r·x + s)` of the period's integer continuant
    matrix; clearing the denominator gives the quadratic
    `r·x² + (s − p)·x − q = 0`.

  • `not_mobius_fixed_point_of_noRatQuadratic` / `cbrt3_not_mobius_fixed_point`
    — since `cbrt3` satisfies **no** nontrivial rational quadratic relation, it
    is the fixed point of **no** non-affine (`r ≠ 0`) rational Möbius
    transformation. Equivalently: **the continued fraction of `cbrt3` is not
    purely periodic** — a single finite obstruction, in place of the open-ended
    per-quotient grind.

  • `mobius_image_noRatQuadratic` — a non-degenerate rational Möbius image of a
    point with no rational quadratic relation again has no rational quadratic
    relation. Infrastructure toward the *eventually*-periodic case (the periodic
    tail, plus a finite prefix Möbius map).

These reduce "the CF of `cbrt3` is not purely periodic" to the single Mathlib-CF
bridge "purely-periodic `IntFractPair.stream cbrt3` ⟹ a non-affine Möbius fixed
point", which is convergent/continuant bookkeeping
(`Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence`, `…Determinant`).
No further *algebraic* content is needed for the purely-periodic obstruction.

All results are abstract in the underlying real and hold for any cubic
irrational; the `cbrt3` corollaries are direct instantiations.

No axioms, no sorries.
-/

import Proofs.CubeRoot3IrrationalOQ04NotQuadratic
import Mathlib

namespace CubeRoot3IrrationalOQ04Mobius

open CubeRoot3Irrational CubeRoot3IrrationalOQ04NotQuadratic

/-- A real `t` satisfies **no nontrivial rational quadratic relation**: the only
rational triple `(a, b, c)` with `a·t² + b·t + c = 0` is `(0, 0, 0)`. This is
exactly "`t` is not a quadratic (or lower-degree) irrational". -/
def NoRatQuadratic (t : ℝ) : Prop :=
  ∀ a b c : ℚ, (a : ℝ) * t ^ 2 + (b : ℝ) * t + (c : ℝ) = 0 → a = 0 ∧ b = 0 ∧ c = 0

/-- `cbrt3` satisfies no nontrivial rational quadratic relation (repackaging of
`cbrt3_not_quadratic`). -/
theorem cbrt3_noRatQuadratic : NoRatQuadratic cbrt3 :=
  fun a b c h => cbrt3_not_quadratic a b c h

/-- **A Möbius fixed point is a quadratic.** If `t` satisfies the
denominator-cleared fixed-point equation `t·(r·t + s) = p·t + q` for rationals
`p q r s`, then `t` is a root of the rational quadratic
`r·X² + (s − p)·X + (−q)`. -/
theorem mobius_fixed_point_quadratic
    (t : ℝ) (p q r s : ℚ)
    (hfix : t * ((r : ℝ) * t + (s : ℝ)) = (p : ℝ) * t + (q : ℝ)) :
    ((r : ℚ) : ℝ) * t ^ 2 + (((s - p : ℚ)) : ℝ) * t + (((-q : ℚ)) : ℝ) = 0 := by
  push_cast
  linear_combination hfix

/-- **No-quadratic ⟹ not a non-affine Möbius fixed point.** If `NoRatQuadratic t`
and the Möbius transformation is genuinely fractional (`r ≠ 0`), then `t` cannot
satisfy `t·(r·t + s) = p·t + q`. -/
theorem not_mobius_fixed_point_of_noRatQuadratic
    (t : ℝ) (ht : NoRatQuadratic t) (p q r s : ℚ) (hr : r ≠ 0)
    (hfix : t * ((r : ℝ) * t + (s : ℝ)) = (p : ℝ) * t + (q : ℝ)) : False := by
  obtain ⟨hr0, _, _⟩ := ht r (s - p) (-q) (mobius_fixed_point_quadratic t p q r s hfix)
  exact hr hr0

/-- **`cbrt3` is the fixed point of no non-affine rational Möbius
transformation** (cleared-denominator form). Equivalently: the continued
fraction of `cbrt3` is not purely periodic. -/
theorem cbrt3_not_mobius_fixed_point (p q r s : ℚ) (hr : r ≠ 0)
    (hfix : cbrt3 * ((r : ℝ) * cbrt3 + (s : ℝ)) = (p : ℝ) * cbrt3 + (q : ℝ)) : False :=
  not_mobius_fixed_point_of_noRatQuadratic cbrt3 cbrt3_noRatQuadratic p q r s hr hfix

/-- **`cbrt3` is not the value of any non-affine rational Möbius transformation
of itself** (division form). For rationals `p q r s` with `r ≠ 0` and nonzero
denominator, `cbrt3 ≠ (p·cbrt3 + q)/(r·cbrt3 + s)`. -/
theorem cbrt3_ne_mobius (p q r s : ℚ) (hr : r ≠ 0)
    (hden : (r : ℝ) * cbrt3 + (s : ℝ) ≠ 0) :
    cbrt3 ≠ ((p : ℝ) * cbrt3 + (q : ℝ)) / ((r : ℝ) * cbrt3 + (s : ℝ)) := by
  intro heq
  rw [eq_div_iff hden] at heq
  exact cbrt3_not_mobius_fixed_point p q r s hr heq

/-- **A non-degenerate rational Möbius image of a no-quadratic point is again a
no-quadratic point.** Suppose `NoRatQuadratic x`, the rational Möbius matrix is
non-degenerate (`a·d − b·c ≠ 0`), the denominator is nonzero (`c·x + d ≠ 0`), and
`y = (a·x + b)/(c·x + d)`. Then `NoRatQuadratic y`.

The transport works by substituting `y` into a hypothetical quadratic
`p·y² + q·y + s = 0` and clearing `(c·x + d)²`, producing the rational quadratic
`A·x² + B·x + C = 0` with
`A = p·a² + q·a·c + s·c²`, `B = 2·p·a·b + q·(a·d + b·c) + 2·s·c·d`,
`C = p·b² + q·b·d + s·d²`. `NoRatQuadratic x` forces `A = B = C = 0`, and the
non-degeneracy `a·d − b·c ≠ 0` then forces `p = q = s = 0` (the coefficient
matrix is the symmetric square of `[[a,b],[c,d]]`, with determinant
`(a·d − b·c)³`). -/
theorem mobius_image_noRatQuadratic
    (x y : ℝ) (hx : NoRatQuadratic x) (a b c d : ℚ)
    (hdet : a * d - b * c ≠ 0)
    (hden : (c : ℝ) * x + (d : ℝ) ≠ 0)
    (hy : y = ((a : ℝ) * x + (b : ℝ)) / ((c : ℝ) * x + (d : ℝ))) :
    NoRatQuadratic y := by
  intro p q s hrel
  -- Clear the denominator in `hy`: `y·(c·x + d) = a·x + b`.
  rw [eq_div_iff hden] at hy
  set A : ℚ := p * a ^ 2 + q * a * c + s * c ^ 2 with hA
  set B : ℚ := 2 * p * a * b + q * (a * d + b * c) + 2 * s * c * d with hB
  set C : ℚ := p * b ^ 2 + q * b * d + s * d ^ 2 with hC
  -- `(p·y² + q·y + s)·(c·x + d)² = A·x² + B·x + C`, using `y·(c·x+d) = a·x+b`.
  have key : ((p : ℝ) * y ^ 2 + (q : ℝ) * y + (s : ℝ)) * ((c : ℝ) * x + (d : ℝ)) ^ 2
      = (A : ℝ) * x ^ 2 + (B : ℝ) * x + (C : ℝ) := by
    simp only [hA, hB, hC]
    push_cast
    linear_combination
      ((p : ℝ) * y * ((c : ℝ) * x + (d : ℝ)) + (p : ℝ) * ((a : ℝ) * x + (b : ℝ))
        + (q : ℝ) * ((c : ℝ) * x + (d : ℝ))) * hy
  rw [hrel, zero_mul] at key
  obtain ⟨hA0, hB0, hC0⟩ := hx A B C key.symm
  rw [hA] at hA0
  rw [hB] at hB0
  rw [hC] at hC0
  have hdet2 : (a * d - b * c) ^ 2 ≠ 0 := pow_ne_zero 2 hdet
  refine ⟨?_, ?_, ?_⟩
  · have hp : p * (a * d - b * c) ^ 2 = 0 := by
      linear_combination d ^ 2 * hA0 - c * d * hB0 + c ^ 2 * hC0
    exact (mul_eq_zero.mp hp).resolve_right hdet2
  · have hq : q * (a * d - b * c) ^ 2 = 0 := by
      linear_combination (-2 * b * d) * hA0 + (a * d + b * c) * hB0 + (-2 * a * c) * hC0
    exact (mul_eq_zero.mp hq).resolve_right hdet2
  · have hs : s * (a * d - b * c) ^ 2 = 0 := by
      linear_combination b ^ 2 * hA0 - a * b * hB0 + a ^ 2 * hC0
    exact (mul_eq_zero.mp hs).resolve_right hdet2

end CubeRoot3IrrationalOQ04Mobius
