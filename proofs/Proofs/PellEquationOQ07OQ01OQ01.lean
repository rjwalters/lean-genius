/-
Pell's Equation OQ-07 → OQ-01 → OQ-01: Determinant Norm Identity and the
Cassini/Catalan Identities for Pell Coordinate Sequences

The grandparent entry (`pell-equation-oq-07`) extracts the second-order recurrence
`uₙ₊₂ = (2x₁)uₙ₊₁ − N(a)·uₙ` obeyed by each coordinate of the power sequence `aⁿ` of
a generating quadratic integer `a = ⟨x₁, y₁⟩ ∈ ℤ√d`. The parent entry
(`pell-equation-oq-07-oq-01`) supplies the *companion-matrix closed form*
`Mⁿ = !![re(aⁿ), d·im(aⁿ); im(aⁿ), re(aⁿ)]` for `M = !![x₁, d·y₁; y₁, x₁]`, with
`tr M = 2x₁` and `det M = N(a)`.

This entry reads the **determinant** off that closed form. Because the determinant is
multiplicative, `det(Mⁿ) = (det M)ⁿ = N(a)ⁿ`; on the other hand, evaluating the
determinant of the explicit power matrix gives `re(aⁿ)² − d·im(aⁿ)²`. Equating the two
recovers the fundamental **norm-power identity**

    re(aⁿ)² − d·im(aⁿ)² = N(a)ⁿ,                         (`norm_pow_eq`)

i.e. `N(aⁿ) = N(a)ⁿ`, obtained here purely from `det(Mⁿ) = (det M)ⁿ`. For a Pell
generator (`N(a) = 1`) this is exactly the Pell equation `xₙ² − d·yₙ² = 1` for every
power — the whole infinite family of Pell solutions in one determinant.

From the same conjugate-symmetric decompositions the parent uses for Binet's formula,
we also derive the **Cassini/Catalan identities** — the "second determinant" of three
consecutive coordinates:

    xₙ·xₙ₊₂ − xₙ₊₁² =  d·y₁²·N(a)ⁿ,                       (`cassini_re`)
    d·(yₙ·yₙ₊₂ − yₙ₊₁²) = −d·y₁²·N(a)ⁿ,                   (`cassini_im`)

where `xₖ = re(aᵏ)`, `yₖ = im(aᵏ)`. These are the two-by-two "consecutive-terms"
determinants of the Pell sequence, and they are `√d`-free: every proof lives inside the
ring `ℤ√d`, using only that conjugation `star` is a ring involution.

## Mechanism

Writing `α = a`, `β = star a`, the parent's isolation lemmas give
`αᵏ + βᵏ = ⟨2xₖ, 0⟩` and `αᵏ − βᵏ = ⟨0, 2yₖ⟩`. The Cassini determinant is the pure
commutative-ring identity

    (αⁿ + βⁿ)(αⁿ⁺² + βⁿ⁺²) − (αⁿ⁺¹ + βⁿ⁺¹)² = (αβ)ⁿ (α − β)²,

and dually with `−` in place of `+` on the left and an overall sign on the right. Since
`αβ = a·star a = ⟨N(a), 0⟩` and `(α − β)² = ⟨4·d·y₁², 0⟩`, reading the rational
coordinate turns each into the stated integer identity.

## Main results

* `mul_star_eq` — `a·star a = ⟨N(a), 0⟩` (Mathlib's `norm_eq_mul_conj`, restated).
* `sub_star_mul_self` — `(a − star a)² = ⟨4·d·y₁², 0⟩`.
* `det_companion_pow` — `det(Mⁿ) = N(a)ⁿ` via `Matrix.det_pow` and `det M = N(a)`.
* `norm_pow_eq` — `re(aⁿ)² − d·im(aⁿ)² = N(a)ⁿ`: the norm-power identity, read off the
  determinant of the companion power form.
* `norm_pow` — the same as `(aⁿ).norm = a.norm ^ n` in Mathlib's `Zsqrtd.norm`.
* `pell_pow` — for a Pell generator, `re(aⁿ)² − d·im(aⁿ)² = 1` for all `n`.
* `cassini_re` / `cassini_im` — the Cassini/Catalan determinants of consecutive
  coordinates.
* Concrete `D = 2` checks against `(3 + 2√2)ⁿ = 1,3,17,99,… / 0,2,12,70,…`: the norm
  identity is the Pell equation `xₙ² − 2yₙ² = 1`, and the Cassini constant is
  `d·y₁² = 2·4 = 8`.

All proofs are `sorry`-free and axiom-free (no `native_decide`).

References:
- Parent: `pell-equation-oq-07-oq-01` (companion-matrix closed form, isolation lemmas).
- Mathlib `Mathlib/NumberTheory/Zsqrtd/Basic.lean` (`norm`, `norm_mul`,
  `norm_eq_mul_conj`, `star`) and `Mathlib/LinearAlgebra/Matrix/Determinant`
  (`Matrix.det_pow`, `Matrix.det_fin_two_of`).
- The Cassini identity `Fₙ₋₁Fₙ₊₁ − Fₙ² = (−1)ⁿ` is the `d = 5`, `a = ⟨1,1⟩/2` shadow of
  this determinant; the general form is the Catalan identity for Lucas sequences.
-/

import Proofs.PellEquationOQ07OQ01

namespace PellEquationOQ07OQ01OQ01

open Zsqrtd Matrix
open PellEquationOQ07OQ01

variable {d : ℤ}

/-
## Two elementary `ℤ√d` identities

The determinant identities all reduce, after using the parent's isolation lemmas, to two
facts about the involution `star`: the product `a · star a` is the norm (a rational
element), and the square of `a − star a` is `4·d·y₁²` (again rational).
-/

/-- **Product with conjugate is the norm.** `a · star a = ⟨N(a), 0⟩`. This is Mathlib's
`Zsqrtd.norm_eq_mul_conj` read as a multiplication rule. -/
theorem mul_star_eq (a : ℤ√d) : a * star a = ((a.norm : ℤ) : ℤ√d) :=
  (Zsqrtd.norm_eq_mul_conj a).symm

/-- **Square of the difference with the conjugate.** `(a − star a)² = ⟨4·d·y₁², 0⟩`:
`a − star a = ⟨0, 2y₁⟩` is purely `√d`, so its square is the rational `d·(2y₁)²`. -/
theorem sub_star_mul_self (a : ℤ√d) :
    (a - star a) * (a - star a) = ((4 * d * a.im ^ 2 : ℤ) : ℤ√d) := by
  refine Zsqrtd.ext ?_ ?_
  · rw [re_mul, re_sub, im_sub, re_star, im_star, re_intCast]; ring
  · rw [im_mul, re_sub, im_sub, re_star, im_star, im_intCast]; ring

/-
## The norm-power identity via the determinant

`det` is multiplicative, so `det(Mⁿ) = (det M)ⁿ = N(a)ⁿ`. Evaluating `det` on the
explicit companion power form `Mⁿ = !![xₙ, d·yₙ; yₙ, xₙ]` gives `xₙ² − d·yₙ²`.
-/

/-- **Determinant of the companion power.** `det(Mⁿ) = N(a)ⁿ`, by multiplicativity of the
determinant (`det(Mⁿ) = (det M)ⁿ`) and `det M = N(a)`. -/
theorem det_companion_pow (a : ℤ√d) (n : ℕ) :
    ((companion a) ^ n).det = a.norm ^ n := by
  rw [Matrix.det_pow, companion_det]

/-- **The norm-power identity.** `re(aⁿ)² − d·im(aⁿ)² = N(a)ⁿ`. Read off by equating the
two evaluations of `det(Mⁿ)`: the closed form `!![xₙ, d·yₙ; yₙ, xₙ]` has determinant
`xₙ² − d·yₙ²`, while multiplicativity gives `N(a)ⁿ`. Equivalently `N(aⁿ) = N(a)ⁿ`. -/
theorem norm_pow_eq (a : ℤ√d) (n : ℕ) :
    (a ^ n).re ^ 2 - d * (a ^ n).im ^ 2 = a.norm ^ n := by
  have hdet := det_companion_pow a n
  rw [companion_pow, Matrix.det_fin_two_of] at hdet
  linear_combination hdet

/-- **Multiplicativity of the norm along powers**, `(aⁿ).norm = a.norm ^ n`, exhibited as
a restatement of `norm_pow_eq` through `Zsqrtd.norm_def`. -/
theorem norm_pow (a : ℤ√d) (n : ℕ) : (a ^ n).norm = a.norm ^ n := by
  rw [Zsqrtd.norm_def]
  have h := norm_pow_eq a n
  linear_combination h

/-- **The Pell equation for every power.** For a Pell generator (`N(a) = 1`), each power
satisfies `re(aⁿ)² − d·im(aⁿ)² = 1`: the companion determinant `det(Mⁿ) = 1ⁿ = 1`
produces the whole infinite family of Pell solutions at once. -/
theorem pell_pow (a : ℤ√d) (h : a.norm = 1) (n : ℕ) :
    (a ^ n).re ^ 2 - d * (a ^ n).im ^ 2 = 1 := by
  rw [norm_pow_eq, h, one_pow]

/-
## The Cassini/Catalan identities

The `2×2` determinant of three consecutive coordinates. Writing `α = a`, `β = star a`,
the parent isolation lemmas turn `2xₖ` into `αᵏ + βᵏ` and `2yₖ` into the `√d`-part of
`αᵏ − βᵏ`, and the identity becomes a pure ring computation whose right-hand side factors
through `αβ = ⟨N(a), 0⟩` and `(α − β)² = ⟨4dy₁², 0⟩`.
-/

/-- Core `ℤ√d` determinant identity (real branch):
`(αⁿ+βⁿ)(αⁿ⁺²+βⁿ⁺²) − (αⁿ⁺¹+βⁿ⁺¹)² = (αβ)ⁿ(α−β)²` with `β = star a`. -/
private theorem cassini_re_elt (a : ℤ√d) (n : ℕ) :
    (a ^ n + star a ^ n) * (a ^ (n + 2) + star a ^ (n + 2))
      - (a ^ (n + 1) + star a ^ (n + 1)) * (a ^ (n + 1) + star a ^ (n + 1))
      = (a * star a) ^ n * ((a - star a) * (a - star a)) := by
  ring

/-- Core `ℤ√d` determinant identity (imaginary branch):
`(αⁿ−βⁿ)(αⁿ⁺²−βⁿ⁺²) − (αⁿ⁺¹−βⁿ⁺¹)² = −(αβ)ⁿ(α−β)²`. -/
private theorem cassini_im_elt (a : ℤ√d) (n : ℕ) :
    (a ^ n - star a ^ n) * (a ^ (n + 2) - star a ^ (n + 2))
      - (a ^ (n + 1) - star a ^ (n + 1)) * (a ^ (n + 1) - star a ^ (n + 1))
      = -((a * star a) ^ n * ((a - star a) * (a - star a))) := by
  ring

/-- **Cassini/Catalan identity, real coordinate.** For `xₖ = re(aᵏ)`,
`xₙ·xₙ₊₂ − xₙ₊₁² = d·y₁²·N(a)ⁿ`. It is the `2×2` determinant `det !![xₙ₊₂, xₙ₊₁; xₙ₊₁, xₙ]`
of consecutive coordinates, evaluated through the conjugate decomposition. -/
theorem cassini_re (a : ℤ√d) (n : ℕ) :
    (a ^ n).re * (a ^ (n + 2)).re - (a ^ (n + 1)).re ^ 2
      = d * a.im ^ 2 * a.norm ^ n := by
  have h := cassini_re_elt a n
  rw [pow_add_star_pow a n, pow_add_star_pow a (n + 1), pow_add_star_pow a (n + 2),
      mul_star_eq, sub_star_mul_self, ← Int.cast_pow] at h
  have hint := congrArg Zsqrtd.re h
  simp only [re_mul, re_sub, re_intCast, im_intCast, mul_zero, add_zero] at hint
  have h4 : (4 : ℤ) * ((a ^ n).re * (a ^ (n + 2)).re - (a ^ (n + 1)).re ^ 2)
      = 4 * (d * a.im ^ 2 * a.norm ^ n) := by linear_combination hint
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4

/-- **Cassini/Catalan identity, `√d` coordinate.** For `yₖ = im(aᵏ)`,
`d·(yₙ·yₙ₊₂ − yₙ₊₁²) = −d·y₁²·N(a)ⁿ`. (Stated with the `d` factor so it also holds at
`d = 0`; for `d ≠ 0` it says `yₙyₙ₊₂ − yₙ₊₁² = −y₁²N(a)ⁿ`.) -/
theorem cassini_im (a : ℤ√d) (n : ℕ) :
    d * ((a ^ n).im * (a ^ (n + 2)).im - (a ^ (n + 1)).im ^ 2)
      = -(d * a.im ^ 2 * a.norm ^ n) := by
  have h := cassini_im_elt a n
  rw [pow_sub_star_pow a n, pow_sub_star_pow a (n + 1), pow_sub_star_pow a (n + 2),
      mul_star_eq, sub_star_mul_self, ← Int.cast_pow] at h
  have hint := congrArg Zsqrtd.re h
  simp only [re_mul, re_sub, re_neg, re_intCast, im_intCast,
    mul_zero, add_zero, zero_add] at hint
  have h4 : (4 : ℤ) * (d * ((a ^ n).im * (a ^ (n + 2)).im - (a ^ (n + 1)).im ^ 2))
      = 4 * (-(d * a.im ^ 2 * a.norm ^ n)) := by linear_combination hint
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4

/-
## Concrete `D = 2` checks

The norm-`1` generator `3 + 2√2 = ⟨3,2⟩ ∈ ℤ[√2]` has power sequence
`x : 1, 3, 17, 99, …` and `y : 0, 2, 12, 70, …`. Here `d·y₁² = 2·2² = 8`.
-/

/-- For `(3+2√2)ⁿ` the norm identity is the **Pell equation** `xₙ² − 2yₙ² = 1`. -/
theorem pell_pow_two (n : ℕ) :
    ((⟨3, 2⟩ : ℤ√2) ^ n).re ^ 2 - 2 * ((⟨3, 2⟩ : ℤ√2) ^ n).im ^ 2 = 1 :=
  pell_pow (⟨3, 2⟩ : ℤ√2) PellEquationOQ07.norm_three_two n

/-- The Pell equation at `n = 2`: `17² − 2·12² = 289 − 288 = 1`. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 2).re ^ 2 - 2 * ((⟨3, 2⟩ : ℤ√2) ^ 2).im ^ 2 = 1 := by decide

/-- The Cassini constant for `⟨3,2⟩` is `d·y₁² = 8`, so `xₙxₙ₊₂ − xₙ₊₁² = 8` for all `n`. -/
theorem cassini_re_two (n : ℕ) :
    ((⟨3, 2⟩ : ℤ√2) ^ n).re * ((⟨3, 2⟩ : ℤ√2) ^ (n + 2)).re
      - ((⟨3, 2⟩ : ℤ√2) ^ (n + 1)).re ^ 2 = 8 := by
  have h := cassini_re (⟨3, 2⟩ : ℤ√2) n
  rw [PellEquationOQ07.norm_three_two, one_pow] at h
  rw [h]; norm_num

/-- Cassini at `n = 0`: `x₀x₂ − x₁² = 1·17 − 3² = 17 − 9 = 8`. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 0).re * ((⟨3, 2⟩ : ℤ√2) ^ 2).re
    - ((⟨3, 2⟩ : ℤ√2) ^ 1).re ^ 2 = 8 := by decide

#check @norm_pow_eq
#check @norm_pow
#check @pell_pow
#check @cassini_re
#check @cassini_im
#check @det_companion_pow

end PellEquationOQ07OQ01OQ01
