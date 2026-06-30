/-
  An explicit imperfect ring (and field): Frobenius is not surjective on 𝔽ₚ[X].

  The grandparent thread (`FrobeniusEndomorphism…`) established that over a
  commutative ring of prime characteristic `p` the Frobenius `x ↦ x ^ p` is a
  ring homomorphism, and the parent (`FrobeniusEndomorphismOQ01OQ02`) showed
  that on a *finite* field the Frobenius is an automorphism — finite fields are
  *perfect*.  The parent's second open question asks us to sharpen the
  perfect-field dichotomy from the other side:

      **Exhibit an explicit imperfect field where Frobenius fails to be
      surjective.**

  This file answers that verbatim with the simplest possible witness.

  * In the polynomial ring `𝔽ₚ[X]` the Frobenius is still *injective* (it is a
    domain, hence reduced, so `frobenius_inj` applies), but it is *not
    surjective*: the indeterminate `X` has no `p`-th root.  Indeed if `f ^ p = X`
    then comparing `natDegree` gives `p · deg f = 1`, forcing `p ∣ 1`,
    impossible for a prime `p ≥ 2`.  So `𝔽ₚ[X]` is an explicit imperfect ring
    (`¬ PerfectRing`).

  * Passing to the fraction field `𝔽ₚ(X) = RatFunc (ZMod p)`, the same `X` still
    has no `p`-th root — now the obstruction is the *integer* degree
    `intDegree`, which is multiplicative on nonzero elements, so `f ^ p = X`
    would give `p · intDegree f = 1` in `ℤ`.  Hence `𝔽ₚ(X)` is an explicit
    imperfect *field* (`¬ PerfectField`), the sharp counterpoint to the
    finite-field case.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.  Built from the
  Mathlib results `frobenius_inj`, `Polynomial.natDegree_pow`,
  `RatFunc.intDegree_mul`, `surjective_frobenius`, and
  `PerfectField.toPerfectRing`.
-/
import Mathlib

namespace FrobeniusEndomorphismOQ01OQ02OQ02

open Polynomial Function

variable (p : ℕ) [Fact p.Prime]

/-! ### Part 1: the polynomial ring `𝔽ₚ[X]` is an explicit imperfect ring -/

/-- The Frobenius `x ↦ xᵖ` is **injective** on `𝔽ₚ[X]`: the polynomial ring over
a field is a domain, hence reduced, and Frobenius is injective on any reduced
ring of characteristic `p`. -/
theorem frobenius_injective_polynomial :
    Injective (frobenius (ZMod p)[X] p) :=
  frobenius_inj (ZMod p)[X] p

/-- The indeterminate `X` has **no `p`-th root** in `𝔽ₚ[X]`: a degree obstruction.
If `f ^ p = X` then `p · natDegree f = 1`, so `p ∣ 1`, impossible for `p` prime. -/
theorem X_isNotPthPower : ¬ ∃ f : (ZMod p)[X], f ^ p = X := by
  rintro ⟨f, hf⟩
  have hpp : p.Prime := Fact.out
  have hdeg : (f ^ p).natDegree = (X : (ZMod p)[X]).natDegree := by rw [hf]
  rw [natDegree_pow, natDegree_X] at hdeg
  -- hdeg : p * f.natDegree = 1
  have hpdvd : p ∣ 1 := ⟨f.natDegree, hdeg.symm⟩
  have hp1 : p = 1 := Nat.dvd_one.mp hpdvd
  exact hpp.one_lt.ne' hp1

/-- Therefore the Frobenius is **not surjective** on `𝔽ₚ[X]`: `X` is not in its
image. -/
theorem frobenius_not_surjective_polynomial :
    ¬ Surjective (frobenius (ZMod p)[X] p) := by
  intro hsurj
  obtain ⟨f, hf⟩ := hsurj X
  rw [frobenius_def] at hf
  exact X_isNotPthPower p ⟨f, hf⟩

/-- `𝔽ₚ[X]` is an **explicit imperfect ring**: the Frobenius is not bijective
(it fails surjectivity). -/
theorem not_perfectRing_polynomial :
    ¬ PerfectRing (ZMod p)[X] p := by
  intro h
  haveI := h
  exact frobenius_not_surjective_polynomial p (surjective_frobenius _ p)

/-! ### Part 2: the rational function field `𝔽ₚ(X)` is an explicit imperfect field -/

/-- The integer degree `intDegree` is multiplicative under powers of a nonzero
rational function: `intDegree (rⁿ) = n · intDegree r`. -/
theorem intDegree_pow (r : RatFunc (ZMod p)) (hr : r ≠ 0) (n : ℕ) :
    (r ^ n).intDegree = (n : ℤ) * r.intDegree := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero k hr) hr, ih]
      push_cast
      ring

/-- The indeterminate `X` has **no `p`-th root** in the rational function field
`𝔽ₚ(X)`.  Now the obstruction lives in `ℤ`: `f ^ p = X` would give
`p · intDegree f = 1`, forcing `(p : ℤ) ∣ 1`, impossible for a prime `p`. -/
theorem ratfunc_X_isNotPthPower :
    ¬ ∃ r : RatFunc (ZMod p), r ^ p = RatFunc.X := by
  rintro ⟨r, hr⟩
  have hpp : p.Prime := Fact.out
  -- `X ≠ 0`, via its degree.
  have hX : (RatFunc.X : RatFunc (ZMod p)) ≠ 0 := by
    intro h
    have hd := RatFunc.intDegree_X (K := ZMod p)
    rw [h, RatFunc.intDegree_zero] at hd
    exact absurd hd (by norm_num)
  -- hence `r ≠ 0`.
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (show p ≠ 0 by exact hpp.ne_zero)] at hr
    exact hX hr.symm
  have hdeg : (r ^ p).intDegree = (RatFunc.X : RatFunc (ZMod p)).intDegree := by rw [hr]
  rw [intDegree_pow p r hr0, RatFunc.intDegree_X] at hdeg
  -- hdeg : (p : ℤ) * r.intDegree = 1
  have hpdvd : (p : ℤ) ∣ 1 := ⟨r.intDegree, hdeg.symm⟩
  have hle : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hpdvd
  have : 2 ≤ p := hpp.two_le
  omega

/-- Therefore the Frobenius is **not surjective** on `𝔽ₚ(X)`. -/
theorem frobenius_not_surjective_ratfunc :
    ¬ Surjective (frobenius (RatFunc (ZMod p)) p) := by
  intro hsurj
  obtain ⟨r, hr⟩ := hsurj RatFunc.X
  rw [frobenius_def] at hr
  exact ratfunc_X_isNotPthPower p ⟨r, hr⟩

/-- **The main result.** `𝔽ₚ(X)` is an explicit *imperfect field*: it is not a
`PerfectField`.  This is the sharp counterpoint to the finite-field case, where
every field is perfect. -/
theorem not_perfectField_ratfunc :
    ¬ PerfectField (RatFunc (ZMod p)) := by
  intro h
  haveI := h
  haveI : PerfectRing (RatFunc (ZMod p)) p := PerfectField.toPerfectRing p
  exact frobenius_not_surjective_ratfunc p (surjective_frobenius _ p)

end FrobeniusEndomorphismOQ01OQ02OQ02
