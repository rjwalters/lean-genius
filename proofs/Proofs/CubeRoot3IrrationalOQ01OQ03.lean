/-
# Eisenstein for `Xⁿ − a` at a composite `a` — the squarefree-at-a-prime criterion
  (OQ-01-OQ-03 of ∛3)

The parent entry **cube-root-3-irrational-oq-01** proves, via Mathlib's
`Polynomial.irreducible_of_eisenstein_criterion` at the prime ideal `(p) ⊆ ℤ`,
that `Xⁿ − p` is irreducible over `ℤ` (and `ℚ`) for every **prime** `p` and every
`n ≥ 1`. That hypothesis — `a` *is itself a prime* — is stronger than Eisenstein
actually needs: Eisenstein at a prime `q` only asks that `q` divide the constant
term to the *first* power. So the criterion applies to `Xⁿ − a` whenever there is
**some** prime `q` with

    q ∣ a    and    q² ∤ a

("`a` is squarefree at `q`"), with no requirement that `a` itself be prime, or
even squarefree overall. This file proves that generalization and specializes it
to constants the prime-only parent cannot reach — e.g. `X² − 6`, `X³ − 12`,
`X² − 24` — where `a` is composite but still carries an exactly-simple prime
factor.

Verification of the Eisenstein hypotheses for `Xⁿ − a` at the witnessing prime
`q` (`hdvd : q ∣ a`, `hndvd : q² ∤ a`):
  * leading coefficient `1 ∉ (q)` — the ideal is proper;
  * every lower coefficient is `0` or `−a`, and `−a ∈ (q)` because `q ∣ a`;
  * the constant coefficient `−a ∉ (q)²`, exactly the hypothesis `q² ∤ a`;
  * `Xⁿ − a` is monic, hence primitive.

The prime case `a = p` of the parent is recovered by taking `q = p` (`p ∣ p`,
`p² ∤ p`). Zero axioms; imports only Mathlib.
-/
import Mathlib

open Polynomial

namespace CubeRoot3IrrationalOQ01OQ03

/- ## The general Eisenstein irreducibility theorem over `ℤ` -/

/-- **Eisenstein at a witnessing prime `q`.** If a prime `q` divides `a` exactly
to the first power (`q ∣ a` but `q² ∤ a`), then `Xⁿ − a` is irreducible over `ℤ`
for every `n ≥ 1`. No primality (or squarefreeness) of `a` itself is required. -/
theorem irreducible_X_pow_sub_C_of_squarefree_at_prime_int
    {a : ℤ} {q : ℕ} (hq : q.Prime) (hdvd : (q : ℤ) ∣ a) (hndvd : ¬ ((q : ℤ) ^ 2 ∣ a))
    {n : ℕ} (hn : 0 < n) :
    Irreducible ((X : ℤ[X]) ^ n - C a) := by
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hq0 : (q : ℤ) ≠ 0 := hqZ.ne_zero
  set P : Ideal ℤ := Ideal.span {(q : ℤ)} with hP
  have hPprime : P.IsPrime := (Ideal.span_singleton_prime hq0).mpr hqZ
  have hmonic : ((X : ℤ[X]) ^ n - C a).Monic := monic_X_pow_sub_C a hn.ne'
  have hdeg : ((X : ℤ[X]) ^ n - C a).degree = n := degree_X_pow_sub_C hn a
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
    · -- `m = 0`: the coefficient is `0 − a = −a ∈ P`, since `q ∣ a`
      have : a ∈ P := Ideal.mem_span_singleton.mpr hdvd
      simpa using P.neg_mem this
    · -- otherwise the coefficient is `0`
      simp
  · -- positive degree
    rw [hdeg]; exact_mod_cast hn
  · -- constant coefficient `−a ∉ P²`, i.e. `q² ∤ a`
    have hc : ((X : ℤ[X]) ^ n - C a).coeff 0 = -a := by
      have hx0 : ((X : ℤ[X]) ^ n).coeff 0 = 0 := by
        rw [coeff_X_pow]; exact if_neg (by omega)
      rw [coeff_sub, hx0, coeff_C_zero, zero_sub]
    rw [hc]
    intro hmem
    rw [Ideal.neg_mem_iff, hP, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    exact hndvd hmem
  · -- primitive, because monic
    exact hmonic.isPrimitive

/- ## Transfer to `ℚ` via Gauss's lemma -/

/-- **`Xⁿ − a` is irreducible over `ℚ`** under the same squarefree-at-a-prime
hypothesis. Gauss's lemma lifts the integer irreducibility, after identifying the
casted polynomial with `Xⁿ − a` over `ℚ`. -/
theorem irreducible_X_pow_sub_C_of_squarefree_at_prime_rat
    {a : ℤ} {q : ℕ} (hq : q.Prime) (hdvd : (q : ℤ) ∣ a) (hndvd : ¬ ((q : ℤ) ^ 2 ∣ a))
    {n : ℕ} (hn : 0 < n) :
    Irreducible ((X : ℚ[X]) ^ n - C (a : ℚ)) := by
  have hprim : ((X : ℤ[X]) ^ n - C a).IsPrimitive :=
    (monic_X_pow_sub_C a hn.ne').isPrimitive
  have hmap : ((X : ℤ[X]) ^ n - C a).map (Int.castRingHom ℚ)
      = (X : ℚ[X]) ^ n - C (a : ℚ) := by
    simp [Polynomial.map_sub, Polynomial.map_pow]
  have hiff := Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim
  rw [← hmap, ← hiff]
  exact irreducible_X_pow_sub_C_of_squarefree_at_prime_int hq hdvd hndvd hn

/- ## The prime case of the parent is a special case -/

/-- Recovering the parent theorem: for a prime `p`, `Xⁿ − p` is irreducible over
`ℤ` — take the witnessing prime `q = p` (`p ∣ p`, and `p² ∤ p`). -/
theorem irreducible_X_pow_sub_C_prime_int {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) :
    Irreducible ((X : ℤ[X]) ^ n - C (p : ℤ)) := by
  refine irreducible_X_pow_sub_C_of_squarefree_at_prime_int hp (dvd_refl _) ?_ hn
  -- `p² ∤ p`: else cancelling one `p` gives `p ∣ 1`, impossible.
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  intro hmem
  rw [sq] at hmem
  have hdvd1 : (p : ℤ) ∣ 1 := by
    have h2 : (p : ℤ) * (p : ℤ) ∣ (p : ℤ) * 1 := by rwa [mul_one]
    exact (mul_dvd_mul_iff_left hpZ.ne_zero).mp h2
  exact hpZ.not_unit (isUnit_of_dvd_one hdvd1)

/- ## Specializations the prime-only parent cannot reach -/

/-- `X² − 6` is irreducible over `ℚ`: `6 = 2·3` is not prime, but it is squarefree
at `q = 2` (`2 ∣ 6`, `4 ∤ 6`). Hence `√6` has degree exactly `2` — irrational. -/
theorem irreducible_X_sq_sub_six_rat :
    Irreducible ((X : ℚ[X]) ^ 2 - C (6 : ℚ)) := by
  have h := irreducible_X_pow_sub_C_of_squarefree_at_prime_rat
    (a := 6) (q := 2) (by norm_num) (by norm_num) (by norm_num) (n := 2) (by norm_num)
  simpa using h

/-- `X³ − 12` is irreducible over `ℚ`: `12 = 2²·3` is neither prime nor squarefree,
but it is squarefree at `q = 3` (`3 ∣ 12`, `9 ∤ 12`). Hence `∛12` has degree `3`. -/
theorem irreducible_X_cubed_sub_twelve_rat :
    Irreducible ((X : ℚ[X]) ^ 3 - C (12 : ℚ)) := by
  have h := irreducible_X_pow_sub_C_of_squarefree_at_prime_rat
    (a := 12) (q := 3) (by norm_num) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  simpa using h

/-- `X² − 24` is irreducible over `ℚ`: `24 = 2³·3` is squarefree at `q = 3`
(`3 ∣ 24`, `9 ∤ 24`). Hence `√24` has degree `2`. (Note `24` is *not* squarefree,
yet the single simple prime factor `3` is all Eisenstein needs.) -/
theorem irreducible_X_sq_sub_twentyfour_rat :
    Irreducible ((X : ℚ[X]) ^ 2 - C (24 : ℚ)) := by
  have h := irreducible_X_pow_sub_C_of_squarefree_at_prime_rat
    (a := 24) (q := 3) (by norm_num) (by norm_num) (by norm_num) (n := 2) (by norm_num)
  simpa using h

end CubeRoot3IrrationalOQ01OQ03
