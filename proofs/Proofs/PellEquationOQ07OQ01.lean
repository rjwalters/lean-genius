/-
Pell's Equation OQ-07 → OQ-01: Binet and Companion-Matrix Closed Forms

The parent entry (`pell-equation-oq-07`, `PellEquationOQ07.lean`, verified) extracts
the *additive shadow* of the multiplicative structure of Pell solutions: each
coordinate of the power sequence `aⁿ` of a generating quadratic integer
`a = ⟨x₁, y₁⟩ ∈ ℤ√d` obeys the second-order recurrence

    uₙ₊₂ = (2·x₁)·uₙ₊₁ − N(a)·uₙ                       (Cayley–Hamilton recurrence)

— and for a Pell solution (`N(a) = 1`) this collapses to `uₙ₊₂ = 2x₁·uₙ₊₁ − uₙ`.
That gives the *step rule* of the sequence. This entry supplies the two **closed
forms** the recurrence is the shadow of:

* a **Binet form** expressing each coordinate of `aⁿ` directly in terms of the
  two conjugate roots `x₁ ± y₁√d` of the characteristic polynomial
  `t² − (2x₁)·t + N(a)`, and
* a **companion-matrix power** form `Mⁿ`, where `M` is the matrix of
  multiplication-by-`a` on the basis `{1, √d}`, whose trace and determinant are
  exactly the `(2x₁, N(a))` coefficients of that characteristic polynomial.

## The mechanism: conjugation is the involution `star`

`ℤ√d` carries the ring involution `star ⟨x, y⟩ = ⟨x, −y⟩` (Mathlib's `StarRing`
instance), i.e. the Galois conjugation `x + y√d ↦ x − y√d`. Because `star` is a
ring homomorphism on the commutative ring `ℤ√d`, it commutes with powers
(`star_pow`). Reading the real and `√d` parts of `aⁿ ± (star a)ⁿ` isolates the two
coordinates:

    aⁿ + (star a)ⁿ = ⟨2·re(aⁿ), 0⟩,        aⁿ − (star a)ⁿ = ⟨0, 2·im(aⁿ)⟩.

Mapping these into `ℝ` through the ring hom `Zsqrtd.lift √d : ℤ√d →+* ℝ`
(`a ↦ a.re + a.im·√d`, defined for `d ≥ 0`) turns them into the classical Binet
formulas, since `lift` sends `a` and `star a` to the conjugate reals
`x₁ + y₁√d` and `x₁ − y₁√d`.

## Main results

* `pow_add_star_pow` / `pow_sub_star_pow` — the conjugate-symmetric decompositions
  `aⁿ ± (star a)ⁿ` inside `ℤ√d` (coordinate isolation; no hypothesis on `d`).
* `re_binet` — `re(aⁿ) = ((x₁+y₁√d)ⁿ + (x₁−y₁√d)ⁿ) / 2`  (`d ≥ 0`).
* `im_binet` — `2·im(aⁿ)·√d = (x₁+y₁√d)ⁿ − (x₁−y₁√d)ⁿ`  (`d ≥ 0`).
* `companion_pow` — `Mⁿ = !![re(aⁿ), d·im(aⁿ); im(aⁿ), re(aⁿ)]` for the
  multiplication-by-`a` matrix `M = !![x₁, d·y₁; y₁, x₁]`.
* `companion_trace` / `companion_det` — `tr M = 2x₁`, `det M = N(a)`: the
  coefficients of the characteristic polynomial `t² − (2x₁)t + N(a)`, whose roots
  are the conjugate units `x₁ ± y₁√d`.
* `companion_det_pell` — `det M = 1` for a Pell generator (norm `1`).
* Concrete `D = 2` checks against the chain `(3 + 2√2)ⁿ` (`1,3,17,99,…` /
  `0,2,12,70,…`): `companion_pow_two`, numeric matrix and Binet examples.

All proofs are `sorry`-free and axiom-free (no `native_decide`).

References:
- Parent entry: `pell-equation-oq-07` (the recurrence these are closed forms of).
- Mathlib `Mathlib/NumberTheory/Zsqrtd/Basic.lean` (`Zsqrtd`, `star`, `norm`,
  `lift`, `re_mul`, `im_mul`).
- Companion matrix / Cayley–Hamilton: roots of `t² − (tr M)t + det M` are the
  eigenvalues `x₁ ± y₁√d` of `M`.
-/

import Proofs.PellEquationOQ07

namespace PellEquationOQ07OQ01

open Zsqrtd

variable {d : ℤ}

/-
## Conjugate-symmetric decomposition inside `ℤ√d`

Conjugation `star : ℤ√d → ℤ√d`, `⟨x,y⟩ ↦ ⟨x,−y⟩`, is a ring involution, so it
commutes with powers (`star_pow`). Adding/subtracting `aⁿ` and `(star a)ⁿ`
isolates the two coordinates of the power sequence.
-/

/-- **Real-part isolation.** `aⁿ + (star a)ⁿ = ⟨2·re(aⁿ), 0⟩`: conjugation fixes the
rational part and negates the `√d` part, so the sum is twice the real coordinate and
purely rational. -/
theorem pow_add_star_pow (a : ℤ√d) (n : ℕ) :
    a ^ n + star a ^ n = ((2 * (a ^ n).re : ℤ) : ℤ√d) := by
  have hstar : star (a ^ n) = star a ^ n := star_pow a n
  refine Zsqrtd.ext ?_ ?_
  · rw [re_add, ← hstar, re_star, re_intCast]; ring
  · rw [im_add, ← hstar, im_star, im_intCast]; ring

/-- **`√d`-part isolation.** `aⁿ − (star a)ⁿ = ⟨0, 2·im(aⁿ)⟩`: the difference cancels
the rational part and doubles the `√d` coordinate. -/
theorem pow_sub_star_pow (a : ℤ√d) (n : ℕ) :
    a ^ n - star a ^ n = (⟨0, 2 * (a ^ n).im⟩ : ℤ√d) := by
  have hstar : star (a ^ n) = star a ^ n := star_pow a n
  refine Zsqrtd.ext ?_ ?_
  · rw [re_sub, ← hstar, re_star]; ring
  · rw [im_sub, ← hstar, im_star]; ring

/-
## The Binet closed forms over `ℝ`

For `d ≥ 0` the assignment `a ↦ a.re + a.im·√d` is the ring homomorphism
`Zsqrtd.lift ⟨√d, _⟩ : ℤ√d →+* ℝ`. It sends `a = ⟨x₁,y₁⟩` and `star a` to the
conjugate reals `x₁ + y₁√d` and `x₁ − y₁√d`, the two roots of the characteristic
polynomial. Applying it to the decompositions above gives Binet's formulas.
-/

/-- The real ring homomorphism `ℤ√d →+* ℝ`, `⟨x,y⟩ ↦ x + y·√d`, for `d ≥ 0`. -/
private noncomputable def toReal (hd : 0 ≤ d) : ℤ√d →+* ℝ :=
  Zsqrtd.lift ⟨Real.sqrt d, Real.mul_self_sqrt (by exact_mod_cast hd : (0 : ℝ) ≤ (d : ℝ))⟩

private theorem toReal_apply (hd : 0 ≤ d) (a : ℤ√d) :
    toReal hd a = (a.re : ℝ) + a.im * Real.sqrt d :=
  Zsqrtd.lift_apply_apply _ a

/-- **Binet's formula for the real coordinate.** For `d ≥ 0` and `a = ⟨x₁,y₁⟩`,
`re(aⁿ) = ((x₁ + y₁√d)ⁿ + (x₁ − y₁√d)ⁿ) / 2` — the average of the `n`-th powers of
the two conjugate roots of `t² − (2x₁)t + N(a)`. -/
theorem re_binet (a : ℤ√d) (hd : 0 ≤ d) (n : ℕ) :
    ((a ^ n).re : ℝ)
      = (((a.re : ℝ) + a.im * Real.sqrt d) ^ n
          + ((a.re : ℝ) - a.im * Real.sqrt d) ^ n) / 2 := by
  have hsa : toReal hd (star a) = (a.re : ℝ) - a.im * Real.sqrt d := by
    rw [toReal_apply, re_star, im_star]; push_cast; ring
  have key : toReal hd (a ^ n) + toReal hd (star a ^ n)
      = ((2 * (a ^ n).re : ℤ) : ℝ) := by
    rw [← map_add, pow_add_star_pow a n, map_intCast]
  rw [map_pow, map_pow, toReal_apply hd a, hsa] at key
  push_cast at key
  linarith [key]

/-- **Binet's formula for the `√d` coordinate.** For `d ≥ 0` and `a = ⟨x₁,y₁⟩`,
`2·im(aⁿ)·√d = (x₁ + y₁√d)ⁿ − (x₁ − y₁√d)ⁿ` — the difference of the `n`-th powers of
the conjugate roots. (Stated multiplicatively so it also holds at `d = 0`.) -/
theorem im_binet (a : ℤ√d) (hd : 0 ≤ d) (n : ℕ) :
    ((a ^ n).im : ℝ) * (2 * Real.sqrt d)
      = ((a.re : ℝ) + a.im * Real.sqrt d) ^ n
          - ((a.re : ℝ) - a.im * Real.sqrt d) ^ n := by
  have hsa : toReal hd (star a) = (a.re : ℝ) - a.im * Real.sqrt d := by
    rw [toReal_apply, re_star, im_star]; push_cast; ring
  have key : toReal hd (a ^ n) - toReal hd (star a ^ n)
      = toReal hd (⟨0, 2 * (a ^ n).im⟩ : ℤ√d) := by
    rw [← map_sub, pow_sub_star_pow a n]
  rw [map_pow, map_pow, toReal_apply hd a, hsa, toReal_apply] at key
  push_cast at key
  linarith [key]

/-
## The companion-matrix closed form

On the basis `{1, √d}`, multiplication by `a = ⟨x₁,y₁⟩` sends `1 ↦ ⟨x₁,y₁⟩` and
`√d ↦ ⟨d·y₁, x₁⟩`, so its matrix is `M = !![x₁, d·y₁; y₁, x₁]`. Powers of `M`
realise multiplication by `aⁿ`, hence carry the coordinates of `aⁿ`.
-/

/-- The multiplication-by-`a` matrix on the basis `{1, √d}`. -/
def companion (a : ℤ√d) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![a.re, d * a.im; a.im, a.re]

/-- **The companion-matrix power form.** `Mⁿ = !![re(aⁿ), d·im(aⁿ); im(aⁿ), re(aⁿ)]`:
the powers of the multiplication matrix carry exactly the coordinates of the power
sequence `aⁿ`. -/
theorem companion_pow (a : ℤ√d) (n : ℕ) :
    (companion a) ^ n
      = !![(a ^ n).re, d * (a ^ n).im; (a ^ n).im, (a ^ n).re] := by
  induction n with
  | zero =>
      simp only [pow_zero, pow_zero, re_one, im_one, mul_zero, Matrix.one_fin_two]
  | succ k ih =>
      have hre : (a ^ (k + 1)).re = (a ^ k).re * a.re + d * (a ^ k).im * a.im := by
        rw [pow_succ, re_mul]
      have him : (a ^ (k + 1)).im = (a ^ k).re * a.im + (a ^ k).im * a.re := by
        rw [pow_succ, im_mul]
      rw [pow_succ, ih, companion, hre, him]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;> ring

/-- **Trace of the companion matrix** equals `2·x₁`, the linear coefficient (with a
sign) of the characteristic polynomial `t² − (2x₁)t + N(a)`. -/
theorem companion_trace (a : ℤ√d) : (companion a).trace = 2 * a.re := by
  rw [companion, Matrix.trace_fin_two_of]; ring

/-- **Determinant of the companion matrix** equals the norm `N(a)`, the constant
coefficient of the characteristic polynomial `t² − (2x₁)t + N(a)`. -/
theorem companion_det (a : ℤ√d) : (companion a).det = a.norm := by
  rw [companion, Matrix.det_fin_two_of, Zsqrtd.norm_def]

/-- For a **Pell generator** (norm `1`) the companion matrix has determinant `1`, so
its characteristic polynomial is `t² − (2x₁)t + 1`, with conjugate-unit roots
`x₁ ± y₁√d`. -/
theorem companion_det_pell (a : ℤ√d) (h : a.norm = 1) : (companion a).det = 1 := by
  rw [companion_det, h]

/-
## Concrete `D = 2` checks

The fundamental norm-`1` unit of `ℤ[√2]` is `3 + 2√2 = ⟨3,2⟩`. Its power sequence
begins `1, 3, 17, 99, 577, …` (real part) and `0, 2, 12, 70, 408, …` (`√2` part).
The companion matrix is `!![3, 4; 2, 3]`.
-/

/-- The `D = 2` companion matrix `M = !![3, 4; 2, 3]` and its power form. -/
theorem companion_pow_two (n : ℕ) :
    (!![3, 4; 2, 3] : Matrix (Fin 2) (Fin 2) ℤ) ^ n
      = !![((⟨3, 2⟩ : ℤ√2) ^ n).re, 2 * ((⟨3, 2⟩ : ℤ√2) ^ n).im;
            ((⟨3, 2⟩ : ℤ√2) ^ n).im, ((⟨3, 2⟩ : ℤ√2) ^ n).re] := by
  have h := companion_pow (⟨3, 2⟩ : ℤ√2) n
  rwa [companion, show ((⟨3, 2⟩ : ℤ√2)).re = 3 from rfl,
    show ((⟨3, 2⟩ : ℤ√2)).im = 2 from rfl, show (2 : ℤ) * 2 = 4 from rfl] at h

/-- The `n = 2` coordinates of `(3+2√2)ⁿ`: `(3+2√2)² = 17 + 12√2`. -/
example : ((⟨3, 2⟩ : ℤ√2) ^ 2).re = 17 ∧ ((⟨3, 2⟩ : ℤ√2) ^ 2).im = 12 := by decide

/-- `M² = !![17, 24; 12, 17]`, matching `(3+2√2)² = 17 + 12√2` via `companion_pow_two`. -/
example : (!![3, 4; 2, 3] : Matrix (Fin 2) (Fin 2) ℤ) ^ 2 = !![17, 24; 12, 17] := by
  rw [pow_two, Matrix.mul_fin_two]; norm_num

/-- The determinant of the `D = 2` companion matrix is `1` (Pell norm). -/
example : (companion (⟨3, 2⟩ : ℤ√2)).det = 1 :=
  companion_det_pell _ PellEquationOQ07.norm_three_two

#check @pow_add_star_pow
#check @pow_sub_star_pow
#check @re_binet
#check @im_binet
#check @companion_pow
#check @companion_trace
#check @companion_det
#check @companion_det_pell
#check @companion_pow_two

end PellEquationOQ07OQ01
