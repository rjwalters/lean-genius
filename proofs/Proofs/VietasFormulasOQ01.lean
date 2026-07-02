/-
# Vieta's Formulas under Root Transformations: Scaling, Translation, and Reciprocals

Vieta's formulas identify the coefficients of a monic polynomial with the
elementary symmetric functions `eₖ` of its roots.  A natural next question,
complementary to the sibling entries on Newton's identities (`OQ02`, `OQ03`,
`OQ03OQ01`) and discriminants (`OQ04`, `OQ03OQ05`), is:

> **When we transform the roots, how do the elementary symmetric functions —
> and hence the coefficients — transform?**

This file treats the three classical transformations of the root set of a monic
polynomial and their effect on Vieta's dictionary:

* **Scaling** `rᵢ ↦ λ·rᵢ`.  Each elementary symmetric function is homogeneous of
  its own degree: `eₖ(λ·r) = λᵏ·eₖ(r)`.  So scaling the roots by `λ` scales the
  coefficient of `xⁿ⁻ᵏ` by `λᵏ`.  This is the general form of the familiar fact
  that `x² − bx + c` with roots `r, s` becomes `x² − λb·x + λ²c` with roots
  `λr, λs`.

* **Translation** `rᵢ ↦ rᵢ + t`.  Shifting every root by `t` composes the
  polynomial with `X − t`: `∏(X − (rᵢ+t)) = (∏(X − rᵢ)) ∘ (X − t)`.  The sum of
  the roots grows by `n·t`, so choosing `t = −(Σrᵢ)/n` (when `n ≠ 0` in the
  field) makes the translated roots sum to zero.  This is exactly the
  **Tschirnhaus substitution** used to *depress* a polynomial (kill its
  sub-leading term) — e.g. `x = y − b/3` for a monic cubic — referenced by the
  `solution-of-cubic` gallery entry.

* **Reciprocal** `rᵢ ↦ 1/rᵢ` (for nonzero roots).  Inverting the roots
  *reverses* Vieta's dictionary: `eₖ(1/r) = e_{n−k}(r)/eₙ(r)`.  For the monic
  quadratic this sends `x² − bx + c` to `x² − (b/c)x + 1/c`; the polynomial is
  self-reciprocal (palindromic) exactly when the product of the roots is `1`.

The scaling law reuses Mathlib's `Multiset.pow_smul_esymm`; the translation and
reciprocal statements are proved from first principles by multiset induction and
by direct field computation, with concrete quadratic and cubic wrappers throughout.

## Main results

* `Multiset.esymm_map_mul_left` — scaling law `eₖ(λ·s) = λᵏ·eₖ(s)`.
* `Multiset.sum_map_add_right` — translated sum `Σ(rᵢ+t) = Σrᵢ + n·t`.
* `Vieta.prod_X_sub_C_translate` — `∏(X − (rᵢ+t)) = (∏(X − rᵢ)) ∘ (X − t)`.
* `Vieta.depressed_translate` — the Tschirnhaus shift makes the roots sum to `0`.
* `Vieta.esymm_reciprocal_two` / `esymm_reciprocal_three` — reciprocal dictionary.
* Concrete `scale_quadratic`, `scale_cubic`, `depress_cubic`, `reciprocal_quadratic`.

## References

- Mathlib.RingTheory.Polynomial.Vieta (`esymm_neg`, `pow_smul_esymm`)
- Tschirnhaus, E. W. von, *Nova methodus* (1683) — elimination by substitution.
-/

import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Factors

open Polynomial Multiset

namespace Multiset

variable {R : Type*} [CommRing R]

/-- **Scaling law for elementary symmetric functions.**  Scaling every entry of a
multiset by `λ` multiplies its degree-`k` elementary symmetric function by `λᵏ`
(each `eₖ` is homogeneous of degree `k`).  This is the root-scaling half of
Vieta's formulas: if `s` are the roots, the coefficient of `xⁿ⁻ᵏ` is scaled by
`λᵏ`.  Generalises Mathlib's `esymm_neg` (the case `λ = −1`). -/
theorem esymm_map_mul_left (s : Multiset R) (lam : R) (k : ℕ) :
    (s.map (fun r => lam * r)).esymm k = lam ^ k * s.esymm k := by
  have h := Multiset.pow_smul_esymm (S := R) lam k s
  simpa only [smul_eq_mul] using h.symm

/-- **Translated sum.**  Shifting every entry of a multiset by a constant `t`
increases its sum by `card • t = n·t`.  This is the sub-leading Vieta
coefficient under a root translation `rᵢ ↦ rᵢ + t`. -/
theorem sum_map_add_right (s : Multiset R) (t : R) :
    (s.map (fun r => r + t)).sum = s.sum + Multiset.card s • t := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.card_cons, succ_nsmul]
    abel

end Multiset

namespace Vieta

variable {R : Type*} [CommRing R]

/-- **Translation composes with `X − t`.**  The monic polynomial whose roots are
the `rᵢ + t` is obtained from `∏(X − rᵢ)` by the substitution `X ↦ X − t`.  This
is the polynomial-level content behind the Tschirnhaus substitution: shifting the
roots is the same as composing with a linear change of variable. -/
theorem prod_X_sub_C_translate (s : Multiset R) (t : R) :
    (s.map fun r => X - C (r + t)).prod
      = (s.map fun r => X - C r).prod.comp (X - C t) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, ih, mul_comp]
    congr 1
    simp only [sub_comp, X_comp, C_comp, C_add]
    ring

/-- **Depression / Tschirnhaus.**  Over a field, translating the roots by
`t = −(Σrᵢ)/n` makes the translated roots sum to zero, provided `n ≠ 0` in the
field.  Equivalently, the substitution kills the sub-leading coefficient of the
monic polynomial — the standard first step in solving cubics and quartics
(`x = y − b/3` for a monic cubic). -/
theorem depressed_translate {K : Type*} [Field K] (s : Multiset K)
    (hc : (Multiset.card s : K) ≠ 0) :
    (s.map (fun r => r + (- s.sum / (Multiset.card s : K)))).sum = 0 := by
  rw [Multiset.sum_map_add_right, nsmul_eq_mul]
  field_simp
  ring

end Vieta

/-! ## Concrete transformations of quadratics and cubics

The general statements above specialise to the familiar textbook rules.  Each is
a ring/field identity in the *roots*, so it holds over any commutative ring (or
field, where inverses appear) and matches the monic-polynomial coefficient rule
by Vieta's formulas. -/

namespace Vieta

section Concrete

variable {R : Type*} [CommRing R]

/-- **Scaling a quadratic.**  If `r, s` are the roots of `x² − bx + c` (so
`b = r+s`, `c = rs`), then `λr, λs` are the roots of `x² − (λb)x + λ²c`:
expanding `(x − λr)(x − λs)` gives the scaled coefficients directly. -/
theorem scale_quadratic (lam r s x : R) :
    (x - lam * r) * (x - lam * s)
      = x ^ 2 - lam * (r + s) * x + lam ^ 2 * (r * s) := by
  ring

/-- **Scaling a cubic.**  Scaling the three roots by `λ` scales `e₁, e₂, e₃` by
`λ, λ², λ³` respectively. -/
theorem scale_cubic (lam r s t x : R) :
    (x - lam * r) * (x - lam * s) * (x - lam * t)
      = x ^ 3 - lam * (r + s + t) * x ^ 2
        + lam ^ 2 * (r * s + r * t + s * t) * x - lam ^ 3 * (r * s * t) := by
  ring

/-- **Sign flip is the `λ = −1` case.**  Negating the roots of a monic quadratic
sends `x² − bx + c` to `x² + bx + c` (roots `−r, −s`), the reflection `x ↦ −x`. -/
theorem negate_quadratic (r s x : R) :
    (x - (-r)) * (x - (-s)) = x ^ 2 + (r + s) * x + r * s := by
  ring

end Concrete

section Field

variable {K : Type*} [Field K]

/-- **Depressing a cubic (concrete).**  For roots `r, s, t`, the Tschirnhaus shift
by `−(r+s+t)/3` makes the shifted roots sum to zero, provided `3 ≠ 0` in `K`
(automatic in characteristic `0`).  This is the `x = y − b/3` substitution that
removes the `x²` term of a monic cubic. -/
theorem depress_cubic (r s t : K) (h3 : (3 : K) ≠ 0) :
    (r - (r + s + t) / 3) + (s - (r + s + t) / 3) + (t - (r + s + t) / 3) = 0 := by
  field_simp
  ring

/-- **Reciprocal of a quadratic.**  If `r, s ≠ 0` are the roots of `x² − bx + c`
(so `b = r+s`, `c = rs ≠ 0`), then `1/r, 1/s` are the roots of
`x² − (b/c)x + 1/c`.  The new sum of roots is `(r+s)/(rs) = e₁/e₂` (the reversed
Vieta data). -/
theorem reciprocal_quadratic_sum (r s : K) (hr : r ≠ 0) (hs : s ≠ 0) :
    r⁻¹ + s⁻¹ = (r + s) / (r * s) := by
  field_simp
  ring

/-- **Reciprocal Vieta dictionary, two roots.**  Inverting both (nonzero) roots
reverses the elementary symmetric functions: multiplying through by the old
product `e₂ = rs`, the new `e₁` recovers the old `e₁`, and the new `e₂` recovers
`1`.  So `e₁' = e₁/e₂` and `e₂' = 1/e₂`. -/
theorem esymm_reciprocal_two (r s : K) (hr : r ≠ 0) (hs : s ≠ 0) :
    (r⁻¹ + s⁻¹) * (r * s) = r + s ∧ (r⁻¹ * s⁻¹) * (r * s) = 1 := by
  refine ⟨?_, ?_⟩
  · field_simp; ring
  · rw [show r⁻¹ * s⁻¹ * (r * s) = (r⁻¹ * r) * (s⁻¹ * s) by ring,
      inv_mul_cancel₀ hr, inv_mul_cancel₀ hs, one_mul]

/-- **Reciprocal Vieta dictionary, three roots.**  For nonzero `r, s, t`,
inverting the roots turns `e₁ ↦ e₂/e₃`, `e₂ ↦ e₁/e₃`, `e₃ ↦ 1/e₃`, i.e. the
elementary symmetric functions are read in reverse.  Stated in cleared-denominator
form (multiplying through by the old product `e₃ = rst`). -/
theorem esymm_reciprocal_three (r s t : K) (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) :
    (r⁻¹ + s⁻¹ + t⁻¹) * (r * s * t) = s * t + r * t + r * s ∧
    (r⁻¹ * s⁻¹ + r⁻¹ * t⁻¹ + s⁻¹ * t⁻¹) * (r * s * t) = r + s + t ∧
    (r⁻¹ * s⁻¹ * t⁻¹) * (r * s * t) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · field_simp; try ring
  · field_simp; try ring
  · rw [show r⁻¹ * s⁻¹ * t⁻¹ * (r * s * t) = (r⁻¹ * r) * (s⁻¹ * s) * (t⁻¹ * t) by ring,
      inv_mul_cancel₀ hr, inv_mul_cancel₀ hs, inv_mul_cancel₀ ht, one_mul, one_mul]

/-- **Self-reciprocal (palindromic) quadratic.**  When the product of the (nonzero)
roots is `1`, inverting the roots returns the same pair swapped (`1/r = s` and
`1/s = r`), so the monic quadratic `x² − (r+s)x + 1` equals its own reciprocal
transform — its coefficient list `1, −(r+s), 1` is palindromic. -/
theorem reciprocal_swap_of_prod_one (r s : K) (h : r * s = 1) :
    r⁻¹ = s ∧ s⁻¹ = r :=
  ⟨inv_eq_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact h)⟩

end Field

end Vieta
