/-
Rational three-square representability: the unconditional half of the
characterization, via Davenport-Cassels.

CONTEXT.  `Proofs.ThreeSquares` proves Legendre's three-square theorem's
**necessity** half axiom-free (`excluded_form_not_sum_three_sq`: a number of the
form `4^a(8b+7)` is never a sum of three *integer* squares) and isolates the
sufficiency half as a single axiom.  `Proofs.ThreeSquaresDavenportCassels` proves,
axiom-free, the **Davenport-Cassels descent** `exists_int_sq_of_rat_sq`: for the
form `x^2+y^2+z^2`, rational representability *implies* integral representability.

This file records what those two facts give *unconditionally* once combined --
i.e. the entire content of the three-square characterization that does **not**
depend on the still-open Hasse-Minkowski (rational solvability) input:

  * `three_rat_sq_iff_three_int_sq`        -- rational <=> integral, an honest
    `Iff` (Davenport-Cassels in both directions; the reverse is trivial);
  * `excluded_form_not_sum_three_rat_sq`   -- **rational necessity**: the excluded
    family `4^a(8b+7)` is not even a sum of three *rational* squares.  The 2-adic
    obstruction is rational, not merely integral;
  * `three_rat_sq_iff_sq_mul` / `three_rat_sq_iff_natSq_mul` -- **square-class
    invariance**: `n` is a sum of three rational squares iff `m^2 n` is.  This is
    the conceptual reason rational three-square representability depends only on
    the squarefree part of `n` (cf. `ThreeSquaresSquarefreeReduction`).

The remaining, genuinely open piece is the *sufficiency* over `ℚ`
(`ThreeSquaresRationalBridge.ThreeSquaresRationalSolvability`), the Hasse-Minkowski
statement absent from Mathlib.  We close with the full characterization
`three_rat_sq_iff_not_excluded`, conditional only on that single hypothesis, whose
necessity half is the unconditional theorem above.

No `axiom`, no `sorry`, no `native_decide`.
-/
import Mathlib
import Proofs.ThreeSquares
import Proofs.ThreeSquaresDavenportCassels
import Proofs.ThreeSquaresRationalBridge

namespace ThreeSquaresRationalNecessity

open ThreeSquares
open ThreeSquaresRationalBridge

/-- **Rational equals integral for three squares (Davenport-Cassels).**

For the form `x^2+y^2+z^2`, an integer `n` is a sum of three *rational* squares
iff it is a sum of three *integer* squares.  The forward direction is the proved,
axiom-free Davenport-Cassels descent `ThreeSquaresDC.exists_int_sq_of_rat_sq`; the
reverse is the trivial inclusion `ℤ ⊆ ℚ`.  Unconditional. -/
theorem three_rat_sq_iff_three_int_sq (n : ℤ) :
    (∃ x y z : ℚ, x ^ 2 + y ^ 2 + z ^ 2 = (n : ℚ)) ↔
      (∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n) :=
  ⟨ThreeSquaresDC.exists_int_sq_of_rat_sq n,
   fun h => ThreeSquaresRationalBridge.rat_sq_of_int_sq h⟩

/-- **Rational necessity (unconditional).**

A number of the excluded form `4^a(8b+7)` is not even a sum of three *rational*
squares.  Equivalently: the 2-adic obstruction that blocks integral
representability already blocks rational representability.  Proof: a rational
representation would, by Davenport-Cassels, produce an integral one, contradicting
the unconditional integral necessity `excluded_form_not_sum_three_sq`. -/
theorem excluded_form_not_sum_three_rat_sq {n : ℕ} (h : IsExcludedForm n) :
    ¬ ∃ x y z : ℚ, x ^ 2 + y ^ 2 + z ^ 2 = (n : ℚ) := by
  intro hrat
  -- Re-cast the rational representation through `ℤ` to match Davenport-Cassels.
  have hrat' : ∃ x y z : ℚ, x ^ 2 + y ^ 2 + z ^ 2 = ((n : ℤ) : ℚ) := by
    obtain ⟨x, y, z, hxyz⟩ := hrat
    exact ⟨x, y, z, by push_cast at hxyz ⊢; exact hxyz⟩
  have hint : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = (n : ℤ) :=
    (three_rat_sq_iff_three_int_sq (n : ℤ)).mp hrat'
  exact excluded_form_not_sum_three_sq h hint

/-- **Square-class invariance (unconditional, rational scalar).**

For a nonzero rational `m`, the rational `n` is a sum of three rational squares
iff `m^2 * n` is.  (Multiply / divide the representation coordinatewise by `m`.) -/
theorem three_rat_sq_iff_sq_mul {n m : ℚ} (hm : m ≠ 0) :
    (∃ x y z : ℚ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔
      (∃ x y z : ℚ, x ^ 2 + y ^ 2 + z ^ 2 = m ^ 2 * n) := by
  constructor
  · rintro ⟨x, y, z, h⟩
    exact ⟨m * x, m * y, m * z, by rw [← h]; ring⟩
  · rintro ⟨x, y, z, h⟩
    refine ⟨x / m, y / m, z / m, ?_⟩
    field_simp
    linear_combination h

/-- **Square-class invariance (unconditional, natural-number scalar).**

For `m ≠ 0`, the natural number `s` is a sum of three rational squares iff
`m^2 * s` is.  This is exactly the rational step underlying the squarefree
reduction `ThreeSquares.three_sq_of_squarefree_rat`: rational three-square
representability is a function of the squarefree part of `n` alone. -/
theorem three_rat_sq_iff_natSq_mul {s m : ℕ} (hm : m ≠ 0) :
    (∃ x y z : ℚ, x ^ 2 + y ^ 2 + z ^ 2 = (s : ℚ)) ↔
      (∃ x y z : ℚ, x ^ 2 + y ^ 2 + z ^ 2 = ((m ^ 2 * s : ℕ) : ℚ)) := by
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  rw [show (((m ^ 2 * s : ℕ) : ℚ)) = (m : ℚ) ^ 2 * (s : ℚ) by push_cast; ring]
  exact three_rat_sq_iff_sq_mul (n := (s : ℚ)) (m := (m : ℚ)) hmq

/-- **Full rational characterization, conditional on Hasse-Minkowski solvability.**

Assuming three-square rational solvability for non-excluded numbers
(`ThreeSquaresRationalBridge.ThreeSquaresRationalSolvability`, the single open
input), `n` is a sum of three rational squares iff it is not of the excluded form
`4^a(8b+7)`.  The necessity (`→`) half is the *unconditional*
`excluded_form_not_sum_three_rat_sq`; only the sufficiency (`←`) half uses the
hypothesis. -/
theorem three_rat_sq_iff_not_excluded
    (hRat : ThreeSquaresRationalSolvability) (n : ℕ) :
    (∃ x y z : ℚ, x ^ 2 + y ^ 2 + z ^ 2 = (n : ℚ)) ↔ ¬ IsExcludedForm n :=
  ⟨fun hx hexc => excluded_form_not_sum_three_rat_sq hexc hx, fun hne => hRat n hne⟩

end ThreeSquaresRationalNecessity
