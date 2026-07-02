/-
  # The discriminant of a cubic via Vieta's formulas
  # (vietas-formulas-oq-04-oq-01)

  ## The Open Question

  The parent entry `vietas-formulas-oq-04` treats the **quadratic** discriminant,
  proving the identity `b² − 4ac = a²(r − s)²` and its consequences (repeated root
  ⇔ `Δ = 0`, sign behaviour over an ordered field). This file answers the child
  open question for the **cubic**:

  > Express the cubic discriminant as `∏_{i<j} (rᵢ − rⱼ)²` and verify that it equals
  > the classical `−4p³ − 27q²` for the depressed cubic `x³ + p·x + q`.

  For a monic cubic with roots `r₁, r₂, r₃` the discriminant is, by definition,

      Δ = (r₁ − r₂)² (r₁ − r₃)² (r₂ − r₃)².

  The elementary symmetric functions of the roots are

      e₁ = r₁ + r₂ + r₃,
      e₂ = r₁r₂ + r₁r₃ + r₂r₃,
      e₃ = r₁r₂r₃,

  and the master identity (a pure polynomial identity, no hypotheses) is

      Δ = e₁²e₂² − 4e₂³ − 4e₁³e₃ + 18 e₁e₂e₃ − 27 e₃².

  Vieta's formulas for `x³ + b·x² + c·x + d` read `e₁ = −b, e₂ = c, e₃ = −d`, so the
  identity specialises to the classical coefficient discriminant

      Δ = b²c² − 4c³ − 4b³d + 18 b c d − 27 d².

  For the **depressed** cubic `x³ + p·x + q` we have `b = 0`, i.e. `e₁ = 0`, and the
  whole expression collapses to

      Δ = −4p³ − 27q²        (since `p = e₂`,  `q = −e₃`).

  We close the loop the same way the parent did for the quadratic: over an integral
  domain `Δ = 0` holds **iff two of the roots coincide**, the cubic analogue of the
  quadratic repeated-root criterion.

  ## Axiom count: 0
-/

import Mathlib

namespace CubicDiscriminant

/-- **The master discriminant identity (over any commutative ring).**
    The cubic discriminant `((r₁−r₂)(r₁−r₃)(r₂−r₃))²` equals the universal polynomial
    in the elementary symmetric functions `e₁ = r₁+r₂+r₃`, `e₂ = r₁r₂+r₁r₃+r₂r₃`,
    `e₃ = r₁r₂r₃`, namely `e₁²e₂² − 4e₂³ − 4e₁³e₃ + 18 e₁e₂e₃ − 27 e₃²`.
    This is a pure `ring` identity requiring no hypotheses. -/
theorem discriminant_eq_esymm {R : Type*} [CommRing R] (r₁ r₂ r₃ : R) :
    ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 =
      (r₁ + r₂ + r₃) ^ 2 * (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) ^ 2
        - 4 * (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) ^ 3
        - 4 * (r₁ + r₂ + r₃) ^ 3 * (r₁ * r₂ * r₃)
        + 18 * (r₁ + r₂ + r₃) * (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) * (r₁ * r₂ * r₃)
        - 27 * (r₁ * r₂ * r₃) ^ 2 := by
  ring

/-- **Discriminant in terms of the coefficients of a monic cubic.**
    If `r₁, r₂, r₃` are the roots of `x³ + b·x² + c·x + d`, so that Vieta's formulas
    give `b = -(r₁+r₂+r₃)`, `c = r₁r₂+r₁r₃+r₂r₃`, `d = -(r₁r₂r₃)`, then the
    discriminant is the classical `b²c² − 4c³ − 4b³d + 18 b c d − 27 d²`. -/
theorem discriminant_eq_coeffs {R : Type*} [CommRing R] (b c d r₁ r₂ r₃ : R)
    (hb : b = -(r₁ + r₂ + r₃))
    (hc : c = r₁ * r₂ + r₁ * r₃ + r₂ * r₃)
    (hd : d = -(r₁ * r₂ * r₃)) :
    ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 =
      b ^ 2 * c ^ 2 - 4 * c ^ 3 - 4 * b ^ 3 * d + 18 * b * c * d - 27 * d ^ 2 := by
  subst hb hc hd; ring

/-- **The depressed-cubic discriminant `Δ = −4p³ − 27q²`.**
    A depressed cubic `x³ + p·x + q` has vanishing quadratic coefficient, i.e. the
    roots satisfy `r₁ + r₂ + r₃ = 0`, together with `p = r₁r₂+r₁r₃+r₂r₃` and
    `q = -(r₁r₂r₃)`. Under these Vieta relations the discriminant collapses to the
    classical `−4p³ − 27q²`. -/
theorem discriminant_depressed {R : Type*} [CommRing R] (p q r₁ r₂ r₃ : R)
    (hsum : r₁ + r₂ + r₃ = 0)
    (hp : p = r₁ * r₂ + r₁ * r₃ + r₂ * r₃)
    (hq : q = -(r₁ * r₂ * r₃)) :
    ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 = -4 * p ^ 3 - 27 * q ^ 2 := by
  -- Eliminate `r₃` via `r₃ = -(r₁ + r₂)`, then it is a pure ring computation.
  have hr3 : r₃ = -(r₁ + r₂) := by linear_combination hsum
  subst hr3 hp hq; ring

/-- **Sum-of-roots-zero form (no `p, q` symbols).**
    Purely in terms of the roots: when `r₁ + r₂ + r₃ = 0` the discriminant equals
    `−4·e₂³ − 27·e₃²`. This is `discriminant_depressed` with `p, q` inlined and is
    the cleanest statement of the depressed identity. -/
theorem discriminant_of_sum_zero {R : Type*} [CommRing R] (r₁ r₂ r₃ : R)
    (hsum : r₁ + r₂ + r₃ = 0) :
    ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 =
      -4 * (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) ^ 3 - 27 * (r₁ * r₂ * r₃) ^ 2 := by
  have hr3 : r₃ = -(r₁ + r₂) := by linear_combination hsum
  subst hr3; ring

/-- **Sanity check: the depressed identity as a numerical instance.**
    The roots `-1, 0, 1` of `x³ - x` (so `p = -1, q = 0`) give discriminant
    `-4·(-1)³ - 27·0² = 4`, and indeed `((-1-0)(-1-1)(0-1))² = ((-1)(-2)(-1))² = 4`. -/
example : ((((-1 : ℤ) - 0) * ((-1) - 1) * (0 - 1)) ^ 2)
    = -4 * (-1 : ℤ) ^ 3 - 27 * (0 : ℤ) ^ 2 := by decide

/-- **The discriminant vanishes iff two roots coincide (over an integral domain).**
    The cubic analogue of the quadratic repeated-root criterion: since the
    discriminant is a product of squared differences, over a domain it is zero
    exactly when some pair of roots is equal. -/
theorem discriminant_eq_zero_iff {R : Type*} [CommRing R] [IsDomain R]
    (r₁ r₂ r₃ : R) :
    ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 = 0 ↔
      r₁ = r₂ ∨ r₁ = r₃ ∨ r₂ = r₃ := by
  rw [pow_eq_zero_iff (n := 2) (by norm_num), mul_eq_zero, mul_eq_zero,
    sub_eq_zero, sub_eq_zero, sub_eq_zero, or_assoc]

/-- **Distinct roots ⇒ nonzero discriminant (over an integral domain).**
    Direct consequence of `discriminant_eq_zero_iff`: three pairwise-distinct roots
    force the discriminant to be nonzero. -/
theorem discriminant_ne_zero_of_distinct {R : Type*} [CommRing R] [IsDomain R]
    {r₁ r₂ r₃ : R} (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃) :
    ((r₁ - r₂) * (r₁ - r₃) * (r₂ - r₃)) ^ 2 ≠ 0 := by
  rw [Ne, discriminant_eq_zero_iff]
  push_neg
  exact ⟨h₁₂, h₁₃, h₂₃⟩

/-- **Depressed repeated-root criterion in `p, q` form (over an integral domain).**
    Combining `discriminant_depressed` with `discriminant_eq_zero_iff`: for a
    depressed cubic the classical quantity `-4p³ - 27q²` vanishes exactly when two
    of the roots coincide. -/
theorem depressed_discriminant_zero_iff {R : Type*} [CommRing R] [IsDomain R]
    (p q r₁ r₂ r₃ : R)
    (hsum : r₁ + r₂ + r₃ = 0)
    (hp : p = r₁ * r₂ + r₁ * r₃ + r₂ * r₃)
    (hq : q = -(r₁ * r₂ * r₃)) :
    -4 * p ^ 3 - 27 * q ^ 2 = 0 ↔ r₁ = r₂ ∨ r₁ = r₃ ∨ r₂ = r₃ := by
  rw [← discriminant_depressed p q r₁ r₂ r₃ hsum hp hq, discriminant_eq_zero_iff]

end CubicDiscriminant
