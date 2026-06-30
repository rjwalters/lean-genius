/-
# ∛3 via Eisenstein's Criterion — and the general prime case (OQ-01 / OQ-02 of ∛3)

The parent gallery entry **cube-root-3-irrational** proves ∛3 ∉ ℚ by the rational
root theorem, and its open questions ask:

  > Is there a Lean proof of Eisenstein's irreducibility criterion? Combined with
  > the rational root theorem, this would give a cleaner algebraic proof of ∛3's
  > irrationality via the degree argument.

This file answers that with the *general* theorem the rational-root approach does
not give. Using Mathlib's `Polynomial.irreducible_of_eisenstein_criterion` at the
prime ideal `(p) ⊆ ℤ`, we prove

    for every prime `p` and every `n ≥ 1`,  Xⁿ − p  is irreducible over ℤ,

and transfer it to ℚ by Gauss's lemma. Specializing `p = 3, n = 3` recovers the
irreducibility of `X³ − 3` (the minimal polynomial of ∛3) — now via Eisenstein
rather than an ad-hoc rational-root computation — and the construction works
uniformly for `X⁵ − 7`, `X² − 5`, and so on. Irreducibility of the degree-`n`
minimal polynomial is strictly stronger than irrationality: it pins the algebraic
degree of `p^{1/n}` at exactly `n`.

Verification of the Eisenstein hypotheses for `Xⁿ − p`:
  * leading coefficient `1 ∉ (p)` — the ideal is proper;
  * every lower coefficient is `0` or `−p`, both in `(p)`;
  * the constant coefficient `−p ∉ (p)²` — else `p² ∣ p`, impossible for a prime;
  * `Xⁿ − p` is monic, hence primitive.

Zero axioms; imports only Mathlib.
-/
import Mathlib

open Polynomial

namespace CubeRoot3IrrationalOQ01

/- ## The general Eisenstein irreducibility theorem over ℤ -/

/-- **Eisenstein's criterion applied to `Xⁿ − p`.** For a prime `p` and `n ≥ 1`,
the polynomial `Xⁿ − p` is irreducible over `ℤ`. -/
theorem irreducible_X_pow_sub_C_prime_int {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) :
    Irreducible ((X : ℤ[X]) ^ n - C (p : ℤ)) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (p : ℤ) ≠ 0 := hpZ.ne_zero
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hP
  have hPprime : P.IsPrime := (Ideal.span_singleton_prime hp0).mpr hpZ
  have hmonic : ((X : ℤ[X]) ^ n - C (p : ℤ)).Monic := monic_X_pow_sub_C (p : ℤ) hn.ne'
  have hdeg : ((X : ℤ[X]) ^ n - C (p : ℤ)).degree = n := degree_X_pow_sub_C hn (p : ℤ)
  apply irreducible_of_eisenstein_criterion hPprime
  · -- leading coefficient `1 ∉ P`
    rw [hmonic.leadingCoeff]
    intro h1
    exact hPprime.ne_top (Ideal.eq_top_of_isUnit_mem P h1 isUnit_one)
  · -- every coefficient below the top degree lies in `P`
    intro m hm
    have hmn : m < n := by rw [hdeg] at hm; exact_mod_cast hm
    rw [coeff_sub, coeff_X_pow, coeff_C]
    rw [if_neg (by omega : ¬ m = n)]
    split_ifs with h0m
    · -- `m = 0`: the coefficient is `0 − p = −p ∈ P`
      simpa using P.neg_mem (Ideal.mem_span_singleton_self (p : ℤ))
    · -- otherwise the coefficient is `0`
      simp
  · -- positive degree
    rw [hdeg]; exact_mod_cast hn
  · -- constant coefficient `−p ∉ P²`
    have hc : ((X : ℤ[X]) ^ n - C (p : ℤ)).coeff 0 = -(p : ℤ) := by
      have hx0 : ((X : ℤ[X]) ^ n).coeff 0 = 0 := by
        rw [coeff_X_pow]; exact if_neg (by omega)
      rw [coeff_sub, hx0, coeff_C_zero, zero_sub]
    rw [hc]
    intro hmem
    rw [Ideal.neg_mem_iff, hP, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    -- `hmem : p² ∣ p`; cancel one factor of `p` to get `p ∣ 1`, contradicting primality
    have hdvd1 : (p : ℤ) ∣ 1 := by
      have h2 : (p : ℤ) * (p : ℤ) ∣ (p : ℤ) * 1 := by rwa [mul_one, ← sq]
      exact (mul_dvd_mul_iff_left hp0).mp h2
    exact hpZ.not_unit (isUnit_of_dvd_one hdvd1)
  · -- primitive, because monic
    exact hmonic.isPrimitive

/- ## Transfer to ℚ via Gauss's lemma -/

/-- **`Xⁿ − p` is irreducible over `ℚ`** for prime `p` and `n ≥ 1.** Gauss's lemma
(`IsPrimitive.Int.irreducible_iff_irreducible_map_cast`) lifts the integer
irreducibility, after identifying the casted polynomial with `Xⁿ − p` over `ℚ`. -/
theorem irreducible_X_pow_sub_C_prime_rat {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) :
    Irreducible ((X : ℚ[X]) ^ n - C (p : ℚ)) := by
  have hprim : ((X : ℤ[X]) ^ n - C (p : ℤ)).IsPrimitive :=
    (monic_X_pow_sub_C (p : ℤ) hn.ne').isPrimitive
  have hmap : ((X : ℤ[X]) ^ n - C (p : ℤ)).map (Int.castRingHom ℚ)
      = (X : ℚ[X]) ^ n - C (p : ℚ) := by
    simp [Polynomial.map_sub, Polynomial.map_pow]
  have hiff := Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim
  rw [← hmap, ← hiff]
  exact irreducible_X_pow_sub_C_prime_int hp hn

/- ## Specialization: the minimal polynomial of ∛3 -/

/-- `X³ − 3` is irreducible over `ℤ` — via Eisenstein at `p = 3`. -/
theorem irreducible_X_cubed_sub_three_int :
    Irreducible ((X : ℤ[X]) ^ 3 - C (3 : ℤ)) := by
  have h := irreducible_X_pow_sub_C_prime_int (p := 3) (n := 3) (by norm_num) (by norm_num)
  simpa using h

/-- `X³ − 3` is irreducible over `ℚ`. This is the minimal polynomial of ∛3, so ∛3
has degree exactly 3 over ℚ — in particular it is irrational. The proof is now
Eisenstein's criterion, answering the parent's open question. -/
theorem irreducible_X_cubed_sub_three_rat :
    Irreducible ((X : ℚ[X]) ^ 3 - C (3 : ℚ)) := by
  have h := irreducible_X_pow_sub_C_prime_rat (p := 3) (n := 3) (by norm_num) (by norm_num)
  simpa using h

/- ## The technique is uniform across primes and exponents -/

/-- `X⁵ − 7` is irreducible over `ℚ` (so `⁵√7` has degree 5). -/
theorem irreducible_X_fifth_sub_seven_rat :
    Irreducible ((X : ℚ[X]) ^ 5 - C (7 : ℚ)) := by
  have h := irreducible_X_pow_sub_C_prime_rat (p := 7) (n := 5) (by norm_num) (by norm_num)
  simpa using h

/-- `X² − 5` is irreducible over `ℚ` (the Eisenstein proof that `√5` is irrational
of degree 2). -/
theorem irreducible_X_sq_sub_five_rat :
    Irreducible ((X : ℚ[X]) ^ 2 - C (5 : ℚ)) := by
  have h := irreducible_X_pow_sub_C_prime_rat (p := 5) (n := 2) (by norm_num) (by norm_num)
  simpa using h

end CubeRoot3IrrationalOQ01
