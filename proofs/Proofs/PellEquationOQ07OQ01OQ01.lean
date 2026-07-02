/-
Pell's Equation OQ-07 → OQ-01 → OQ-01: Cassini and Catalan Identities

The grandparent entry (`pell-equation-oq-07`) extracted the second-order
recurrence `uₙ₊₂ = (2·x₁)·uₙ₊₁ − N(a)·uₙ` obeyed by both coordinate sequences
`xₙ = re(aⁿ)`, `yₙ = im(aⁿ)` of the power sequence of a generating quadratic
integer `a = ⟨x₁, y₁⟩ ∈ ℤ√d`. The parent entry (`pell-equation-oq-07-oq-01`)
supplied the two closed forms — Binet's formula and the companion-matrix power
`Mⁿ = !![xₙ, d·yₙ; yₙ, xₙ]`, whose determinant is `N(a)ⁿ`.

This entry supplies the **Cassini/Catalan-type determinant identities** these
closed forms carry. Two distinct phenomena:

* **The two-sequence norm identity** (`re_sq_sub_im_sq`):
  `xₙ² − d·yₙ² = N(a)ⁿ`. This is `det(Mⁿ) = (det M)ⁿ = N(a)ⁿ` read off the
  companion power — the multiplicativity of the norm along the power sequence.

* **The single-sequence Catalan identity** (`re_catalan`):
  `xₘ·xₘ₊₂ᵣ − xₘ₊ᵣ² = N(a)ᵐ · d · yᵣ²`, with the **Cassini** special case
  `r = 1` (`re_cassini`): `xₙ·xₙ₊₂ − xₙ₊₁² = N(a)ⁿ · d · y₁²`. For a Pell
  generator (`N(a) = 1`) this collapses to the *constant* `xₙ·xₙ₊₂ − xₙ₊₁² =
  d·y₁²`, independent of `n` — the exact analogue of `Fₙ₋₁Fₙ₊₁ − Fₙ² = (−1)ⁿ`.

## The mechanism: conjugate algebra, no reals

Both identities are proved purely inside `ℤ√d` (valid for **every** `d ∈ ℤ`, no
sign or nonsquare hypothesis) using the ring involution `star` (Galois
conjugation) from the parent. Writing `ā = star a` and using the parent's
coordinate-isolation lemmas
`aᵏ + āᵏ = ⟨2xₖ, 0⟩` and `aᵏ − āᵏ = ⟨0, 2yₖ⟩`, the Catalan identity reduces to a
single polynomial identity in `u = aᵐ, ū = āᵐ, v = aʳ, v̄ = āʳ`:

    (u+ū)(u·v² + ū·v̄²) − (u·v + ū·v̄)²  =  (u·ū)·(v − v̄)²

(a `ring` fact), together with `u·ū = (a·ā)ᵐ = N(a)ᵐ`. Reading the real part and
cancelling the factor `4` gives the integer identity. The `im`-Cassini
identity `yₙ·yₙ₊₂ − yₙ₊₁² = −N(a)ⁿ·y₁²` is proved by induction from the parent
recurrence (avoiding the `d`-factor that the coordinate isolation introduces on
the `√d` axis).

## Main results

* `mul_star_self` — `a · star a = ⟨N(a), 0⟩` (norm as the conjugate product).
* `re_catalan` — `xₘ·xₘ₊₂ᵣ − xₘ₊ᵣ² = N(a)ᵐ · d · yᵣ²`  (all `d, m, r`).
* `re_cassini` — the `r = 1` case `xₙ·xₙ₊₂ − xₙ₊₁² = N(a)ⁿ · d · y₁²`.
* `im_cassini` — `yₙ·yₙ₊₂ − yₙ₊₁² = −N(a)ⁿ · y₁²`  (all `d`).
* `re_cassini_pell` / `im_cassini_pell` — the Pell (`N(a) = 1`) collapse to the
  `n`-independent constants `d·y₁²` and `−y₁²`.
* `re_sq_sub_im_sq` — `xₙ² − d·yₙ² = N(a)ⁿ` via `det(Mⁿ) = (det M)ⁿ`.
* Concrete `D = 2` checks against `(3 + 2√2)ⁿ` (`x : 1,3,17,99,577`,
  `y : 0,2,12,70,408`): Cassini constant `d·y₁² = 8`, det identity, examples.

All proofs are `sorry`-free and axiom-free (no `native_decide`).

References:
- Parent: `pell-equation-oq-07-oq-01` (`PellEquationOQ07OQ01.lean`) — companion
  matrix and coordinate isolation.
- Grandparent: `pell-equation-oq-07` (`PellEquationOQ07.lean`) — the recurrence.
- Classical: Cassini (1680) and Catalan (1879) identities for Fibonacci numbers;
  here for the coordinate sequences of powers of a quadratic integer.
-/

import Proofs.PellEquationOQ07OQ01

namespace PellEquationOQ07OQ01OQ01

open Zsqrtd PellEquationOQ07OQ01 PellEquationOQ07

variable {d : ℤ}

/-
## The conjugate product

Multiplication by the Galois conjugate `star a = ⟨x₁, −y₁⟩` recovers the norm:
`a · star a = ⟨x₁² − d·y₁², 0⟩ = ⟨N(a), 0⟩`.
-/

/-- **The conjugate product is the norm.** `a · star a = ⟨N(a), 0⟩`, the integer
cast of the norm `N(a) = x₁² − d·y₁²`. -/
theorem mul_star_self (a : ℤ√d) : a * star a = ((a.norm : ℤ) : ℤ√d) := by
  refine Zsqrtd.ext ?_ ?_
  · simp only [re_mul, re_star, im_star, re_intCast, Zsqrtd.norm_def]; ring
  · simp only [im_mul, re_star, im_star, im_intCast]; ring

/-- `aᵐ · (star a)ᵐ = ⟨N(a)ᵐ, 0⟩`: the conjugate product distributes over powers. -/
theorem pow_mul_star_pow (a : ℤ√d) (m : ℕ) :
    a ^ m * star a ^ m = ((a.norm ^ m : ℤ) : ℤ√d) := by
  rw [← mul_pow, mul_star_self, Int.cast_pow]

/-
## The Catalan identity for the rational coordinate

`xₘ·xₘ₊₂ᵣ − xₘ₊ᵣ² = N(a)ᵐ · d · yᵣ²`. The core is a polynomial identity in the
conjugate pairs, extracted through the coordinate-isolation lemmas of the parent.
-/

/-- **Catalan's identity for the `re` sequence.** For all `d ∈ ℤ` and all `m, r`,
`re(aᵐ)·re(aᵐ⁺²ʳ) − re(aᵐ⁺ʳ)² = N(a)ᵐ · d · im(aʳ)²`. The right side depends on
`m` only through the factor `N(a)ᵐ`; the shape `d·im(aʳ)²` is the Catalan
"defect" at offset `r`. -/
theorem re_catalan (a : ℤ√d) (m r : ℕ) :
    (a ^ m).re * (a ^ (m + 2 * r)).re - (a ^ (m + r)).re ^ 2
      = a.norm ^ m * (d * (a ^ r).im ^ 2) := by
  -- Power splittings in terms of u = aᵐ, v = aʳ and their conjugates.
  have e1 : a ^ (m + r) = a ^ m * a ^ r := pow_add a m r
  have e2 : a ^ (m + 2 * r) = a ^ m * (a ^ r) ^ 2 := by
    rw [pow_add, mul_comm 2 r, pow_mul]
  have es1 : star a ^ (m + r) = star a ^ m * star a ^ r := pow_add _ m r
  have es2 : star a ^ (m + 2 * r) = star a ^ m * (star a ^ r) ^ 2 := by
    rw [pow_add, mul_comm 2 r, pow_mul]
  -- Master identity inside ℤ√d, RHS collected as a single integer cast.
  have master :
      (((2 * (a ^ m).re : ℤ) : ℤ√d)) * (((2 * (a ^ (m + 2 * r)).re : ℤ) : ℤ√d))
          - (((2 * (a ^ (m + r)).re : ℤ) : ℤ√d)) ^ 2
        = ((a.norm ^ m * (d * (2 * (a ^ r).im) ^ 2) : ℤ) : ℤ√d) := by
    rw [← pow_add_star_pow a m, ← pow_add_star_pow a (m + 2 * r),
      ← pow_add_star_pow a (m + r)]
    have hval :
        a ^ m * star a ^ m * (a ^ r - star a ^ r) ^ 2
          = ((a.norm ^ m * (d * (2 * (a ^ r).im) ^ 2) : ℤ) : ℤ√d) := by
      rw [pow_mul_star_pow, pow_sub_star_pow a r]
      refine Zsqrtd.ext ?_ ?_ <;>
        simp only [re_mul, im_mul, re_intCast, im_intCast, pow_two, mul_zero,
          zero_mul, add_zero, mul_comm] <;> ring
    rw [← hval, e2, es2, e1, es1]
    ring
  -- Extract the real part: casts collapse to their integer arguments.
  have hre := congrArg Zsqrtd.re master
  simp only [re_sub, re_mul, re_intCast, im_intCast, pow_two, mul_zero,
    add_zero] at hre
  -- hre now equals 4·(goal_lhs) = 4·(goal_rhs); cancel the 4.
  have h4 : (4 : ℤ) * ((a ^ m).re * (a ^ (m + 2 * r)).re - (a ^ (m + r)).re ^ 2)
      = 4 * (a.norm ^ m * (d * (a ^ r).im ^ 2)) := by linear_combination hre
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4

/-- **Cassini's identity for the `re` sequence** (`r = 1` of `re_catalan`).
`re(aⁿ)·re(aⁿ⁺²) − re(aⁿ⁺¹)² = N(a)ⁿ · d · y₁²`, where `y₁ = im a`. -/
theorem re_cassini (a : ℤ√d) (n : ℕ) :
    (a ^ n).re * (a ^ (n + 2)).re - (a ^ (n + 1)).re ^ 2
      = a.norm ^ n * (d * a.im ^ 2) := by
  have h := re_catalan a n 1
  simpa using h

/-
## The Cassini identity for the `√d` coordinate

The coordinate isolation on the `√d` axis introduces a factor of `d`, so instead
we prove `yₙ·yₙ₊₂ − yₙ₊₁² = −N(a)ⁿ·y₁²` by induction from the parent recurrence,
keeping it valid for every `d` (including `d = 0`).
-/

/-- **Cassini's identity for the `im` sequence.** For all `d ∈ ℤ`,
`im(aⁿ)·im(aⁿ⁺²) − im(aⁿ⁺¹)² = −N(a)ⁿ · y₁²`, where `y₁ = im a`. -/
theorem im_cassini (a : ℤ√d) (n : ℕ) :
    (a ^ n).im * (a ^ (n + 2)).im - (a ^ (n + 1)).im ^ 2
      = -(a.norm ^ n * a.im ^ 2) := by
  induction n with
  | zero =>
      simp only [pow_zero, im_one, zero_mul, pow_succ, one_mul]
      ring
  | succ k ih =>
      -- Recurrence at indices k and k+1.
      have r1 := Zsqrtd.im_recurrence a k
      have r2 := Zsqrtd.im_recurrence a (k + 1)
      -- Goal: y_{k+1}·y_{k+3} − y_{k+2}² = −N^{k+1}·y₁²; reduce to N·(ih LHS).
      have key : (a ^ (k + 1)).im * (a ^ (k + 1 + 2)).im - (a ^ (k + 1 + 1)).im ^ 2
          = a.norm * ((a ^ k).im * (a ^ (k + 2)).im - (a ^ (k + 1)).im ^ 2) := by
        have e2 : (a ^ (k + 1 + 2)).im = 2 * a.re * (a ^ (k + 1 + 1)).im - a.norm * (a ^ (k + 1)).im := r2
        have e1 : (a ^ (k + 2)).im = 2 * a.re * (a ^ (k + 1)).im - a.norm * (a ^ k).im := r1
        rw [e2]
        have hc : (a ^ (k + 1 + 1)).im = (a ^ (k + 2)).im := by norm_num
        rw [hc, e1]
        ring
      rw [key, ih, pow_succ]
      ring

/-
## The Pell collapse (`N(a) = 1`)

For a Pell generator the norm powers `N(a)ⁿ` are all `1`, so the Cassini defects
become the `n`-independent constants `d·y₁²` and `−y₁²` — the closest analogue of
the Fibonacci `Fₙ₋₁Fₙ₊₁ − Fₙ² = (−1)ⁿ`, here with a *constant* right-hand side.
-/

/-- **Pell Cassini for the `re` sequence.** When `N(a) = 1`,
`re(aⁿ)·re(aⁿ⁺²) − re(aⁿ⁺¹)² = d·y₁²` for all `n` — a constant independent of `n`. -/
theorem re_cassini_pell (a : ℤ√d) (h : a.norm = 1) (n : ℕ) :
    (a ^ n).re * (a ^ (n + 2)).re - (a ^ (n + 1)).re ^ 2 = d * a.im ^ 2 := by
  rw [re_cassini a n, h, one_pow, one_mul]

/-- **Pell Cassini for the `im` sequence.** When `N(a) = 1`,
`im(aⁿ)·im(aⁿ⁺²) − im(aⁿ⁺¹)² = −y₁²` for all `n`. -/
theorem im_cassini_pell (a : ℤ√d) (h : a.norm = 1) (n : ℕ) :
    (a ^ n).im * (a ^ (n + 2)).im - (a ^ (n + 1)).im ^ 2 = -(a.im ^ 2) := by
  rw [im_cassini a n, h, one_pow, one_mul]

/-
## The two-sequence norm identity via the companion determinant

Reading `det(Mⁿ) = (det M)ⁿ = N(a)ⁿ` off the companion power
`Mⁿ = !![xₙ, d·yₙ; yₙ, xₙ]` gives the norm of every power: `xₙ² − d·yₙ² = N(a)ⁿ`.
This is the multiplicativity `N(aⁿ) = N(a)ⁿ`, obtained here through the matrix
determinant rather than by hand.
-/

/-- **The norm of every power via the companion determinant.**
`re(aⁿ)² − d·im(aⁿ)² = N(a)ⁿ`, i.e. `N(aⁿ) = N(a)ⁿ`, read off
`det(Mⁿ) = (det M)ⁿ = N(a)ⁿ`. -/
theorem re_sq_sub_im_sq (a : ℤ√d) (n : ℕ) :
    (a ^ n).re ^ 2 - d * (a ^ n).im ^ 2 = a.norm ^ n := by
  have hdet : ((companion a) ^ n).det = a.norm ^ n := by
    rw [Matrix.det_pow, companion_det]
  rw [companion_pow, Matrix.det_fin_two_of] at hdet
  linear_combination hdet

/-- For a Pell generator every power is again a Pell solution:
`re(aⁿ)² − d·im(aⁿ)² = 1`. -/
theorem re_sq_sub_im_sq_pell (a : ℤ√d) (h : a.norm = 1) (n : ℕ) :
    (a ^ n).re ^ 2 - d * (a ^ n).im ^ 2 = 1 := by
  rw [re_sq_sub_im_sq a n, h, one_pow]

/-
## Concrete `D = 2` checks

The fundamental norm-`1` unit of `ℤ[√2]` is `3 + 2√2 = ⟨3, 2⟩`, with `y₁ = 2`, so
the Pell Cassini constants are `d·y₁² = 2·4 = 8` (real part) and `−y₁² = −4`
(`√2` part). Power sequence: `x : 1, 3, 17, 99, 577`, `y : 0, 2, 12, 70, 408`.
-/

/-- The `re`-Cassini constant for `(3+2√2)` is `d·y₁² = 8`: e.g. `x₀x₂ − x₁² =
1·17 − 9 = 8` and `x₁x₃ − x₂² = 3·99 − 289 = 8`. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 0).re * ((⟨3, 2⟩ : ℤ√2) ^ 2).re
    - ((⟨3, 2⟩ : ℤ√2) ^ 1).re ^ 2 = 8 := by decide

example : ((⟨3, 2⟩ : ℤ√2) ^ 1).re * ((⟨3, 2⟩ : ℤ√2) ^ 3).re
    - ((⟨3, 2⟩ : ℤ√2) ^ 2).re ^ 2 = 8 := by decide

/-- The `im`-Cassini constant for `(3+2√2)` is `−y₁² = −4`: `y₀y₂ − y₁² =
0·12 − 4 = −4`. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 0).im * ((⟨3, 2⟩ : ℤ√2) ^ 2).im
    - ((⟨3, 2⟩ : ℤ√2) ^ 1).im ^ 2 = -4 := by decide

/-- Every power of `(3+2√2)` is a Pell solution: `x₃² − 2·y₃² = 99² − 2·70² =
9801 − 9800 = 1`. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 3).re ^ 2 - 2 * ((⟨3, 2⟩ : ℤ√2) ^ 3).im ^ 2 = 1 := by decide

/-- The general Cassini defect at `(3+2√2)`, offset `r = 2`: `d·y₂² = 2·144 = 288`
(`re_catalan` with `r = 2`, `m = 0`): `x₀x₄ − x₂² = 1·577 − 289 = 288`. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 0).re * ((⟨3, 2⟩ : ℤ√2) ^ 4).re
    - ((⟨3, 2⟩ : ℤ√2) ^ 2).re ^ 2 = 288 := by decide

#check @mul_star_self
#check @re_catalan
#check @re_cassini
#check @im_cassini
#check @re_cassini_pell
#check @im_cassini_pell
#check @re_sq_sub_im_sq
#check @re_sq_sub_im_sq_pell

end PellEquationOQ07OQ01OQ01
