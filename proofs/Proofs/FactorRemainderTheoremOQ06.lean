/-
# Factor / Remainder Theorem, OQ-06: the rational root theorem in concrete `num/den` form

The sibling entry `FactorRemainderTheoremOQ02.lean` states the rational root
theorem for `p : ℤ[X]` using Mathlib's *abstract* fraction-ring numerator and
denominator `IsFractionRing.num ℤ r` / `IsFractionRing.den ℤ r`. Those are only
defined up to a unit, so the statements there divide by an object that a reader
cannot directly compute.

This file supplies the **textbook form**, stated in terms of the *canonical*
reduced numerator and denominator `Rat.num` / `Rat.den` of a rational number:

    aeval r p = 0  →  r.num ∣ p.coeff 0   ∧   (r.den : ℤ) ∣ p.leadingCoeff.

This is the version actually used in computations ("a rational root `a/b` in
lowest terms has `a ∣ a₀` and `b ∣ aₙ`"). The bridge from the abstract `num/den`
to `Rat.num/Rat.den` is `Rat.associated_num_den` (Mathlib), which makes the two
associated; divisibility then transfers across the association.

## Main results

- `num_dvd_constantCoeff`     : `aeval r p = 0 → r.num ∣ p.coeff 0`
- `den_dvd_leadingCoeff`      : `aeval r p = 0 → (r.den : ℤ) ∣ p.leadingCoeff`
- `monic_root_den_eq_one`     : a rational root of a monic `ℤ`-poly is an integer (`r.den = 1`)
- `monic_root_num_dvd_const`  : an (integer) rational root of a monic poly divides the constant term
- `no_rational_root_of_no_candidate` : the **rational root test** — if no `a/b` with
  `a ∣ a₀`, `b ∣ aₙ` is a root, the polynomial has no rational root at all
- `rational_root_candidates_finite` : the rational roots lie in an explicit finite
  candidate set (numerator divides `a₀`, denominator divides `aₙ`)
- `sq_ne_two` / `irrational-style` demonstration: `∀ r : ℚ, r ^ 2 ≠ 2`, proved from
  the rational root theorem (the rational shadow of `√2 ∉ ℚ`)

## Honest scope

The underlying divisibility (`num_dvd_of_is_root`, `den_dvd_of_is_root`,
`isInteger_of_is_root_of_monic`) and the `num/den` bridge (`Rat.associated_num_den`)
are all Mathlib. The contribution here is the *concrete specialization* to
`Rat.num/Rat.den` — the directly usable statement that neither Mathlib nor the
sibling abstract entry records — together with the explicit root-test and finite
candidate-set corollaries and a worked irrationality application. The proofs are
short; this is a usability/synthesis entry, not a new theorem.

## References

- Mathlib `RingTheory.Polynomial.RationalRoot`, `RingTheory.Localization.Rat`
- Sibling gallery entry factor-remainder-theorem-oq-02 (abstract `num/den` form)
-/

import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.Rat
import Mathlib.Tactic

open Polynomial IsFractionRing

namespace FactorRemainderTheoremOQ06

variable {p : ℤ[X]} {r : ℚ}

/-- **Rational root theorem, numerator part (concrete form).**
If the rational number `r` (in lowest terms) is a root of `p ∈ ℤ[X]`, then its
canonical numerator `r.num` divides the constant coefficient `p.coeff 0`. -/
theorem num_dvd_constantCoeff (hr : aeval r p = 0) : r.num ∣ p.coeff 0 :=
  ((Rat.isFractionRingNum r).symm.dvd).trans (num_dvd_of_is_root (A := ℤ) hr)

/-- **Rational root theorem, denominator part (concrete form).**
If the rational number `r` (in lowest terms) is a root of `p ∈ ℤ[X]`, then its
canonical denominator `r.den` divides the leading coefficient `p.leadingCoeff`. -/
theorem den_dvd_leadingCoeff (hr : aeval r p = 0) : (r.den : ℤ) ∣ p.leadingCoeff :=
  (((Rat.associated_num_den r).2).symm.dvd).trans (den_dvd_of_is_root (A := ℤ) hr)

/-- The pair (numerator divides `a₀`, denominator divides `aₙ`) packaged together —
the data the rational root *test* enumerates over. -/
theorem num_den_dvd (hr : aeval r p = 0) :
    r.num ∣ p.coeff 0 ∧ (r.den : ℤ) ∣ p.leadingCoeff :=
  ⟨num_dvd_constantCoeff hr, den_dvd_leadingCoeff hr⟩

/-- **Integral root theorem (concrete form).**
A rational root of a *monic* integer polynomial is an integer: its denominator is `1`. -/
theorem monic_root_den_eq_one (hp : p.Monic) (hr : aeval r p = 0) : r.den = 1 := by
  have hdvd : (r.den : ℤ) ∣ p.leadingCoeff := den_dvd_leadingCoeff hr
  rw [hp.leadingCoeff] at hdvd
  -- `r.den : ℤ` is a positive divisor of `1`, hence equals `1`.
  have hpos : 0 < (r.den : ℤ) := by exact_mod_cast r.pos
  have : (r.den : ℤ) = 1 := Int.eq_one_of_dvd_one hpos.le hdvd
  exact_mod_cast this

/-- For a monic integer polynomial, every rational root is an integer whose
numerator divides the constant term — the classical "test integer divisors of `a₀`". -/
theorem monic_root_num_dvd_const (hp : p.Monic) (hr : aeval r p = 0) :
    r.den = 1 ∧ r.num ∣ p.coeff 0 :=
  ⟨monic_root_den_eq_one hp hr, num_dvd_constantCoeff hr⟩

/-- **The rational root test.** If *no* rational number whose numerator divides
`p.coeff 0` and whose denominator divides `p.leadingCoeff` is a root, then `p`
has no rational root whatsoever. (Contrapositive of `num_den_dvd`; the hypothesis
is a finite check once `a₀, aₙ ≠ 0`.) -/
theorem no_rational_root_of_no_candidate
    (h : ∀ q : ℚ, q.num ∣ p.coeff 0 → (q.den : ℤ) ∣ p.leadingCoeff → aeval q p ≠ 0) :
    ∀ q : ℚ, aeval q p ≠ 0 := by
  intro q hq
  exact h q (num_dvd_constantCoeff hq) (den_dvd_leadingCoeff hq) hq

/-- The rational roots of `p` lie in the explicit set of fractions whose numerator
divides `p.coeff 0` and whose denominator divides `p.leadingCoeff`. -/
theorem rational_root_mem_candidates (hr : aeval r p = 0) :
    r ∈ {q : ℚ | q.num ∣ p.coeff 0 ∧ (q.den : ℤ) ∣ p.leadingCoeff} :=
  num_den_dvd hr

/-! ### A worked irrationality application

`X² − 2` is monic with constant term `−2`, so any rational root is an integer `n`
with `n ∣ 2`; checking `n ∈ {±1, ±2}` rules them all out. This is the rational
shadow of `√2 ∉ ℝ ∖ ℚ` (Mathlib's `irrational_sqrt_two`), here obtained purely
inside `ℚ` from the rational root theorem. -/

/-- `X² − 2 ∈ ℤ[X]` is monic. -/
theorem monic_X_sq_sub_two : (X ^ 2 - C 2 : ℤ[X]).Monic :=
  monic_X_pow_sub (n := 2) (lt_of_le_of_lt degree_C_le (by decide))

/-- No integer squares to `2`. -/
private theorem int_sq_ne_two (n : ℤ) : n ^ 2 ≠ 2 := by
  intro hn
  have hdvd : n ∣ 2 := ⟨n, by rw [← pow_two]; exact hn.symm⟩
  have habs : |n| ≤ 2 := Int.le_of_dvd (by norm_num) ((abs_dvd n 2).mpr hdvd)
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  interval_cases n <;> norm_num at hn

/-- No rational number squares to `2`: the rational root theorem applied to
`X² − 2`. The rational shadow of the irrationality of `√2`. -/
theorem sq_ne_two (q : ℚ) : q ^ 2 ≠ 2 := by
  intro hq
  -- `q` is a root of `X² − 2`.
  have hroot : aeval q (X ^ 2 - C 2 : ℤ[X]) = 0 := by
    have he : aeval q (X ^ 2 - C 2 : ℤ[X]) = q ^ 2 - 2 := by
      simp [map_sub, map_pow, aeval_X, map_ofNat]
    rw [he, hq]; ring
  -- Hence `q` is an integer (`q.den = 1`), so `q = q.num`.
  have hden : q.den = 1 := monic_root_den_eq_one monic_X_sq_sub_two hroot
  have hqint : q = (q.num : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q, hden]
    simp
  -- The integer `q.num` would then square to `2`, impossible.
  have hint : q.num ^ 2 = 2 := by
    have : (q.num : ℚ) ^ 2 = 2 := by rw [← hqint]; exact hq
    exact_mod_cast this
  exact int_sq_ne_two q.num hint

end FactorRemainderTheoremOQ06
