/-
Pell's Equation OQ-07 → OQ-01 → OQ-01: Cassini / Catalan Identities from `det(Mⁿ) = (det M)ⁿ`

The grandparent entry (`pell-equation-oq-07`) extracted the second-order recurrence
of the coordinate sequences of the power chain `aⁿ` of a quadratic integer
`a = ⟨x₁, y₁⟩ ∈ ℤ√d`; the parent (`pell-equation-oq-07-oq-01`,
`PellEquationOQ07OQ01.lean`, verified) supplied the two **closed forms** — the Binet
formula and the **companion-matrix power** `Mⁿ = !![re(aⁿ), d·im(aⁿ); im(aⁿ), re(aⁿ)]`
for `M = !![x₁, d·y₁; y₁, x₁]`, with `tr M = 2x₁`, `det M = N(a)`.

This entry closes the open question left by the parent: **the multiplicative content
of the companion form**. Because determinant is multiplicative,

    det(Mⁿ) = (det M)ⁿ = N(a)ⁿ,                              (`det_companion_pow`)

and reading `det(Mⁿ)` off the explicit power form gives the **quadratic Pell
invariant** — the classical Cassini identity for Pell chains:

    re(aⁿ)² − d·im(aⁿ)² = N(a)ⁿ.                             (`re_sq_sub_d_im_sq`)

For a Pell generator (`N(a) = 1`) this says *every power of a Pell solution is again a
Pell solution* (`pow_isPell`). From the one-step recurrence
`re(aⁿ⁺¹) = x₁·re(aⁿ) + d·y₁·im(aⁿ)`, `im(aⁿ⁺¹) = y₁·re(aⁿ) + x₁·im(aⁿ)`
(the shadow of `aⁿ⁺¹ = a·aⁿ`) together with that invariant, the genuine three-term
Cassini/Catalan identities fall out:

    re(aⁿ)·im(aⁿ⁺¹) − re(aⁿ⁺¹)·im(aⁿ) = y₁·N(a)ⁿ,             (`cross_cassini`)
    re(aⁿ)·re(aⁿ⁺²) − re(aⁿ⁺¹)²        =  d·y₁²·N(a)ⁿ,        (`cassini_re`)
    im(aⁿ)·im(aⁿ⁺²) − im(aⁿ⁺¹)²        = −y₁²·N(a)ⁿ.          (`cassini_im`)

The three-term identities are the Catalan-type invariants `uₙ₋₁uₙ₊₁ − uₙ² = c·N(a)ⁿ⁻¹`
(re-indexed to start at `n`) for the two coordinate sequences, with the constant `c`
determined by the seed `y₁ = im(a)`. All of this is pure integer algebra in `ℤ√d` and
`Matrix (Fin 2) (Fin 2) ℤ`; no passage to `ℝ` or `√d` is needed.

## Main results

* `det_companion_pow` — `det(Mⁿ) = N(a)ⁿ` (`Matrix.det_pow` + parent `companion_det`).
* `re_sq_sub_d_im_sq` — the Pell quadratic invariant `re(aⁿ)² − d·im(aⁿ)² = N(a)ⁿ`,
  obtained by evaluating `det(Mⁿ)` two ways.
* `pow_isPell` — powers of a Pell solution (`N(a) = 1`) are Pell solutions.
* `cross_cassini` — the mixed two-coordinate Cassini invariant `y₁·N(a)ⁿ`.
* `cassini_re` / `cassini_im` — the three-term Cassini/Catalan identities for the real
  and `√d` coordinate sequences.
* Concrete `D = 2` checks against `(3 + 2√2)ⁿ` (`re: 1,3,17,99,…`, `im: 0,2,12,70,…`,
  `N = 1`).

References:
- Parent: `pell-equation-oq-07-oq-01` (`companion_pow`, `companion_det`).
- Grandparent: `pell-equation-oq-07` (the recurrence).
- Mathlib `Matrix.det_pow`, `Matrix.det_fin_two_of`; `Zsqrtd.norm`, `re_mul`, `im_mul`.
-/

import Proofs.PellEquationOQ07OQ01

namespace PellEquationOQ07OQ01OQ01

open Zsqrtd PellEquationOQ07OQ01

variable {d : ℤ}

/-
## The determinant identity `det(Mⁿ) = N(a)ⁿ`

Determinant is a monoid homomorphism, so `det(Mⁿ) = (det M)ⁿ`; the parent computed
`det M = N(a)`.
-/

/-- **`det(Mⁿ) = N(a)ⁿ`.** The determinant of the `n`-th power of the multiplication
matrix is the `n`-th power of the norm, since `det` is multiplicative and
`det M = N(a)` (parent `companion_det`). -/
theorem det_companion_pow (a : ℤ√d) (n : ℕ) :
    ((companion a) ^ n).det = a.norm ^ n := by
  rw [Matrix.det_pow, companion_det]

/-
## The quadratic Pell invariant (Cassini for Pell chains)

Evaluating `det(Mⁿ)` on the explicit power form `!![rₙ, d·sₙ; sₙ, rₙ]` gives
`rₙ² − d·sₙ²`; equating with `N(a)ⁿ` yields the invariant. Here
`rₙ = re(aⁿ)`, `sₙ = im(aⁿ)`.
-/

/-- **The Pell quadratic invariant.** `re(aⁿ)² − d·im(aⁿ)² = N(a)ⁿ`: reading the
determinant of `Mⁿ = !![re(aⁿ), d·im(aⁿ); im(aⁿ), re(aⁿ)]` off the explicit power form
and equating with `det(Mⁿ) = N(a)ⁿ`. (This is `Zsqrtd.norm (aⁿ) = N(a)ⁿ` recovered
through the companion determinant.) -/
theorem re_sq_sub_d_im_sq (a : ℤ√d) (n : ℕ) :
    (a ^ n).re ^ 2 - d * (a ^ n).im ^ 2 = a.norm ^ n := by
  have h := det_companion_pow a n
  rw [companion_pow, Matrix.det_fin_two_of] at h
  linear_combination h

/-- **Powers of a Pell solution are Pell solutions.** If `N(a) = 1` then
`re(aⁿ)² − d·im(aⁿ)² = 1` for every `n`: the norm-`1` locus is closed under powers. -/
theorem pow_isPell (a : ℤ√d) (h : a.norm = 1) (n : ℕ) :
    (a ^ n).re ^ 2 - d * (a ^ n).im ^ 2 = 1 := by
  rw [re_sq_sub_d_im_sq, h, one_pow]

/-
## The three-term Cassini / Catalan identities

The one-step recurrence `aⁿ⁺¹ = a·aⁿ` reads, on coordinates,
`re(aⁿ⁺¹) = re(a)·re(aⁿ) + d·im(a)·im(aⁿ)` and
`im(aⁿ⁺¹) = re(a)·im(aⁿ) + im(a)·re(aⁿ)`. Combining these with the quadratic invariant
gives the Cassini invariants.
-/

/-- One-step real-coordinate recurrence `re(aⁿ⁺¹) = re(a)·re(aⁿ) + d·im(a)·im(aⁿ)`. -/
private theorem re_succ (a : ℤ√d) (n : ℕ) :
    (a ^ (n + 1)).re = a.re * (a ^ n).re + d * a.im * (a ^ n).im := by
  rw [pow_succ, re_mul]; ring

/-- One-step `√d`-coordinate recurrence `im(aⁿ⁺¹) = re(a)·im(aⁿ) + im(a)·re(aⁿ)`. -/
private theorem im_succ (a : ℤ√d) (n : ℕ) :
    (a ^ (n + 1)).im = a.re * (a ^ n).im + a.im * (a ^ n).re := by
  rw [pow_succ, im_mul]; ring

/-- **Mixed two-coordinate Cassini invariant.**
`re(aⁿ)·im(aⁿ⁺¹) − re(aⁿ⁺¹)·im(aⁿ) = im(a)·N(a)ⁿ`. The cross-term of the two
coordinate sequences collapses — via the one-step recurrence and the quadratic
invariant — onto `im(a)·(re(aⁿ)² − d·im(aⁿ)²) = im(a)·N(a)ⁿ`. -/
theorem cross_cassini (a : ℤ√d) (n : ℕ) :
    (a ^ n).re * (a ^ (n + 1)).im - (a ^ (n + 1)).re * (a ^ n).im
      = a.im * a.norm ^ n := by
  have hinv := re_sq_sub_d_im_sq a n
  rw [re_succ, im_succ]
  linear_combination a.im * hinv

/-- **Three-term Cassini/Catalan identity, real coordinate.**
`re(aⁿ)·re(aⁿ⁺²) − re(aⁿ⁺¹)² = d·im(a)²·N(a)ⁿ`. -/
theorem cassini_re (a : ℤ√d) (n : ℕ) :
    (a ^ n).re * (a ^ (n + 2)).re - (a ^ (n + 1)).re ^ 2
      = d * a.im ^ 2 * a.norm ^ n := by
  have hinv := re_sq_sub_d_im_sq a n
  rw [show n + 2 = (n + 1) + 1 from rfl, re_succ a (n + 1), re_succ a n, im_succ a n]
  linear_combination (d * a.im ^ 2) * hinv

/-- **Three-term Cassini/Catalan identity, `√d` coordinate.**
`im(aⁿ)·im(aⁿ⁺²) − im(aⁿ⁺¹)² = −im(a)²·N(a)ⁿ`. -/
theorem cassini_im (a : ℤ√d) (n : ℕ) :
    (a ^ n).im * (a ^ (n + 2)).im - (a ^ (n + 1)).im ^ 2
      = - a.im ^ 2 * a.norm ^ n := by
  have hinv := re_sq_sub_d_im_sq a n
  rw [show n + 2 = (n + 1) + 1 from rfl, im_succ a (n + 1), re_succ a n, im_succ a n]
  linear_combination (- a.im ^ 2) * hinv

/-
## Concrete `D = 2` checks

The fundamental norm-`1` unit of `ℤ[√2]` is `3 + 2√2 = ⟨3,2⟩`, with
`re: 1, 3, 17, 99, …`, `im: 0, 2, 12, 70, …`, and `N = 1`. The Cassini constants are
`d·im(a)² = 2·4 = 8` (real) and `−im(a)² = −4` (`√d`), independent of `n` since
`N(a) = 1`.
-/

/-- Quadratic invariant at `D = 2`, `n = 3`: `re = 99`, `im = 70`, and
`99² − 2·70² = 9801 − 9800 = 1 = N(⟨3,2⟩)³`. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 3).re ^ 2 - 2 * ((⟨3, 2⟩ : ℤ√2) ^ 3).im ^ 2 = 1 := by
  decide

/-- Real three-term Cassini at `D = 2`, `n = 0`: `re₀·re₂ − re₁² = 1·17 − 3² = 8
= 2·2²·1`. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 0).re * ((⟨3, 2⟩ : ℤ√2) ^ 2).re
    - ((⟨3, 2⟩ : ℤ√2) ^ 1).re ^ 2 = 8 := by decide

/-- `√d` three-term Cassini at `D = 2`, `n = 1`: `im₁·im₃ − im₂² = 2·70 − 12² = −4
= −2²·1`. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 1).im * ((⟨3, 2⟩ : ℤ√2) ^ 3).im
    - ((⟨3, 2⟩ : ℤ√2) ^ 2).im ^ 2 = -4 := by decide

/-- Mixed Cassini at `D = 2`, `n = 2`: `re₂·im₃ − re₃·im₂ = 17·70 − 99·12 = 2 = im(a)·N³`. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 2).re * ((⟨3, 2⟩ : ℤ√2) ^ 3).im
    - ((⟨3, 2⟩ : ℤ√2) ^ 3).re * ((⟨3, 2⟩ : ℤ√2) ^ 2).im = 2 := by decide

#check @det_companion_pow
#check @re_sq_sub_d_im_sq
#check @pow_isPell
#check @cross_cassini
#check @cassini_re
#check @cassini_im

end PellEquationOQ07OQ01OQ01
