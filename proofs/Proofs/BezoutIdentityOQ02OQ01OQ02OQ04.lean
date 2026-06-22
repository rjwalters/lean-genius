/-
# Eisenstein's criterion over an arbitrary integral domain (Bézout OQ-02-01-02-04)

The parent entry **bezout-identity-oq-02-oq-01-oq-02** ("FTA Generalization to
Euclidean Domains") develops unique factorization in the abstract UFD / Euclidean-
domain setting, and asks, as its fourth open question:

  > The Eisenstein criterion for irreducibility of polynomials over UFDs is a key
  > application of the UFD framework. Is it formalized in Mathlib, and can it be
  > used here?

Yes — and it works far beyond UFDs. Mathlib's `Polynomial.irreducible_of_eisenstein_criterion`
applies at any prime ideal of any commutative ring. This file packages it into the
clean headline theorem

    for any **integral domain** `R` and any **prime** `p : R`, and any `n ≥ 1`,
    `Xⁿ − p` is irreducible over `R[X]`,

via Eisenstein at the prime ideal `(p)`. Specializing the domain shows the
criterion in genuinely different settings:

  * `R = ℤ`: `Yⁿ − 2` and `Yⁿ − 3` are irreducible over `ℤ[Y]`;
  * `R = ℚ[X]` (a Euclidean domain, exactly the parent's theme): `Yⁿ − X` is
    irreducible over `ℚ[X][Y]` — Eisenstein at the prime element `X`.

This is the same Eisenstein argument used for `∛3` (entry cube-root-3-irrational-oq-01)
but with `ℤ` replaced by an arbitrary integral domain, answering OQ-04 in the full
generality the UFD/Euclidean-domain framework invites.

Zero axioms; imports only Mathlib.
-/
import Mathlib

open Polynomial

namespace BezoutIdentityOQ02OQ01OQ02OQ04

/- ## The general theorem -/

/-- **Eisenstein's criterion for `Xⁿ − p` over any integral domain.** For an
integral domain `R`, a prime element `p : R`, and `n ≥ 1`, the polynomial
`Xⁿ − p` is irreducible in `R[X]`. The four Eisenstein hypotheses at the prime
ideal `(p)`: the leading coefficient `1 ∉ (p)`; every lower coefficient is `0` or
`−p`, both in `(p)`; the constant `−p ∉ (p)²` (else `p² ∣ p`, impossible for a
prime); and `Xⁿ − p` is monic, hence primitive. -/
theorem irreducible_X_pow_sub_C_of_prime {R : Type*} [CommRing R] [IsDomain R]
    {p : R} (hp : Prime p) {n : ℕ} (hn : 0 < n) :
    Irreducible ((X : R[X]) ^ n - C p) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  set P : Ideal R := Ideal.span {p} with hP
  have hPprime : P.IsPrime := (Ideal.span_singleton_prime hp0).mpr hp
  have hmonic : ((X : R[X]) ^ n - C p).Monic := monic_X_pow_sub_C p hn.ne'
  have hdeg : ((X : R[X]) ^ n - C p).degree = n := degree_X_pow_sub_C hn p
  apply irreducible_of_eisenstein_criterion hPprime
  · -- leading coefficient `1 ∉ P`
    rw [hmonic.leadingCoeff]
    intro h1
    exact hPprime.ne_top (Ideal.eq_top_of_isUnit_mem P h1 isUnit_one)
  · -- coefficients below the top degree lie in `P`
    intro m hm
    have hmn : m < n := by rw [hdeg] at hm; exact_mod_cast hm
    rw [coeff_sub, coeff_X_pow, coeff_C, if_neg (by omega : ¬ m = n)]
    split_ifs with h0m
    · simpa using P.neg_mem (Ideal.mem_span_singleton_self p)
    · simp
  · -- positive degree
    rw [hdeg]; exact_mod_cast hn
  · -- constant coefficient `−p ∉ P²`
    have hc : ((X : R[X]) ^ n - C p).coeff 0 = -p := by
      have hx0 : ((X : R[X]) ^ n).coeff 0 = 0 := by
        rw [coeff_X_pow]; exact if_neg (by omega)
      rw [coeff_sub, hx0, coeff_C_zero, zero_sub]
    rw [hc]
    intro hmem
    rw [Ideal.neg_mem_iff, hP, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    have hdvd1 : p ∣ 1 := by
      have h2 : p * p ∣ p * 1 := by rwa [mul_one, ← sq]
      exact (mul_dvd_mul_iff_left hp0).mp h2
    exact hp.not_unit (isUnit_of_dvd_one hdvd1)
  · -- primitive, because monic
    exact hmonic.isPrimitive

/- ## The criterion in different domains -/

/-- Over `ℤ`: `Yⁿ − 2` is irreducible — Eisenstein at the prime `2`. -/
theorem irreducible_Y_pow_sub_two_int {n : ℕ} (hn : 0 < n) :
    Irreducible ((X : ℤ[X]) ^ n - C 2) :=
  irreducible_X_pow_sub_C_of_prime Int.prime_two hn

/-- Over `ℤ`: `Yⁿ − 3` is irreducible — Eisenstein at the prime `3`. -/
theorem irreducible_Y_pow_sub_three_int {n : ℕ} (hn : 0 < n) :
    Irreducible ((X : ℤ[X]) ^ n - C 3) :=
  irreducible_X_pow_sub_C_of_prime Int.prime_three hn

/-- **Over the Euclidean domain `ℚ[X]`:** `Yⁿ − X` is irreducible in `ℚ[X][Y]` —
Eisenstein at the prime element `X`. This is the parent's setting (a Euclidean
domain that is not `ℤ`), and exhibits an irreducible giving the function-field
extension `ℚ(X)(X^{1/n})`. -/
theorem irreducible_Y_pow_sub_X_ratPoly {n : ℕ} (hn : 0 < n) :
    Irreducible ((X : (Polynomial ℚ)[X]) ^ n - C (Polynomial.X)) :=
  irreducible_X_pow_sub_C_of_prime (Polynomial.prime_X) hn

/-- Specialization to the cubic over `ℚ[X]`: `Y³ − X` is irreducible. -/
theorem irreducible_Y_cubed_sub_X_ratPoly :
    Irreducible ((X : (Polynomial ℚ)[X]) ^ 3 - C (Polynomial.X)) :=
  irreducible_Y_pow_sub_X_ratPoly (by norm_num)

end BezoutIdentityOQ02OQ01OQ02OQ04
