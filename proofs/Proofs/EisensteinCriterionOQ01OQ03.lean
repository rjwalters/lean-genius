/-
  Eisenstein's criterion for GENERAL integer polynomials, and irreducibility over ℚ.

  The companion entry `eisenstein-criterion-oq-01` restates the abstract criterion
  (over an arbitrary integral domain, phrased with a prime ideal `P`) and carries
  out the concrete coefficient bookkeeping for the single family `Xⁿ − p`.

  This file answers its third open question:

    > Generalize the coefficient bookkeeping to Eisenstein-at-`p` polynomials with
    > arbitrary lower coefficients divisible by `p` (general `IsEisensteinAt`
    > instances).

  We do three genuinely new things relative to the parent.

  **1. Concrete general criterion over `ℤ`.**  We trade the abstract ideal
  hypotheses for plain divisibility by a prime integer `p`: a monic `f` of positive
  degree with `p ∣ f.coeff k` for every `k` below the degree and `p² ∤ f.coeff 0`
  is irreducible over `ℤ`.  The lower coefficients are completely arbitrary subject
  to divisibility by `p`.

  **2. The general Eisenstein family `Xⁿ + p·g`.**  Concretely, for *any* `g` with
  `deg g < n` and `p ∤ g.coeff 0`, the polynomial `Xⁿ + p·g` is Eisenstein at `p`.
  This is the "arbitrary lower coefficients" the parent could not reach — e.g.
  `X² + 2X + 2`, `X³ + 3X + 3` — and it specializes back to `Xⁿ − p` at `g = −1`.

  **3. Irreducibility over `ℚ` (Gauss's lemma).**  Eisenstein's criterion earns its
  keep precisely because it produces irreducibility over `ℚ`: a monic integer
  Eisenstein polynomial is irreducible in `ℚ[X]`, so it is the minimal polynomial of
  each of its roots and `[ℚ(α):ℚ] = deg f`.  The parent only proves irreducibility
  over `ℤ`; here we cross Gauss's lemma
  (`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`, with `ℚ` the
  fraction field of `ℤ`) to land in `ℚ[X]`.

  Everything is fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open Polynomial

namespace EisensteinCriterionOQ01OQ03

/-! ### Eisenstein's criterion for general integer polynomials -/

/-- Local restatement of Mathlib's abstract Eisenstein criterion
(`Polynomial.irreducible_of_eisenstein_criterion`), used below. -/
theorem aux_irreducible_of_eisenstein {R : Type*} [CommRing R] [IsDomain R]
    {f : R[X]} {P : Ideal R} (hP : P.IsPrime)
    (hlead : f.leadingCoeff ∉ P)
    (hlow : ∀ k : ℕ, (k : WithBot ℕ) < f.degree → f.coeff k ∈ P)
    (hdeg : 0 < f.degree)
    (hconst : f.coeff 0 ∉ P ^ 2)
    (hprim : f.IsPrimitive) : Irreducible f :=
  irreducible_of_eisenstein_criterion hP hlead hlow hdeg hconst hprim

/-- **Eisenstein's criterion over `ℤ`, concrete divisibility form.**
A monic integer polynomial `f` of positive degree, all of whose coefficients below
the leading one are divisible by a prime `p`, and whose constant term is *not*
divisible by `p²`, is irreducible over `ℤ`.

The lower coefficients are arbitrary subject to `p ∣ f.coeff k`; this generalizes
the `Xⁿ − p` family of the parent entry, where the only nonzero lower coefficient is
the constant term. -/
theorem irreducible_int_of_eisenstein {f : ℤ[X]} {p : ℤ} (hp : Prime p)
    (hmonic : f.Monic) (hdeg : 0 < f.natDegree)
    (hlow : ∀ k < f.natDegree, p ∣ f.coeff k)
    (hconst : ¬ (p ^ 2 ∣ f.coeff 0)) :
    Irreducible f := by
  have hP : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hdeg' : f.degree = (f.natDegree : WithBot ℕ) := degree_eq_natDegree hmonic.ne_zero
  refine aux_irreducible_of_eisenstein hP ?_ ?_ ?_ ?_ hmonic.isPrimitive
  · -- leading coefficient `1 ∉ (p)`
    rw [hmonic.leadingCoeff, Ideal.mem_span_singleton]
    exact fun h => hp.not_unit (isUnit_of_dvd_one h)
  · -- every lower coefficient lies in `(p)`
    intro k hk
    rw [hdeg'] at hk
    have hkn : k < f.natDegree := by exact_mod_cast hk
    rw [Ideal.mem_span_singleton]
    exact hlow k hkn
  · -- positive degree
    rw [hdeg']; exact_mod_cast hdeg
  · -- constant coefficient `∉ (p²)`
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hconst

/-- **A monic integer Eisenstein polynomial is irreducible over `ℚ`.**
Crossing Gauss's lemma (`ℚ` is the fraction field of `ℤ`) upgrades irreducibility
over `ℤ` to irreducibility over `ℚ`. This is the form in which Eisenstein's
criterion is actually used: such an `f` is the minimal polynomial of each of its
roots, giving `[ℚ(α) : ℚ] = deg f`. -/
theorem irreducible_rat_of_eisenstein {f : ℤ[X]} {p : ℤ} (hp : Prime p)
    (hmonic : f.Monic) (hdeg : 0 < f.natDegree)
    (hlow : ∀ k < f.natDegree, p ∣ f.coeff k)
    (hconst : ¬ (p ^ 2 ∣ f.coeff 0)) :
    Irreducible (f.map (algebraMap ℤ ℚ)) :=
  (hmonic.irreducible_iff_irreducible_map_fraction_map).mp
    (irreducible_int_of_eisenstein hp hmonic hdeg hlow hconst)

/-! ### The general Eisenstein family `Xⁿ + p·g`

For any `g` with `deg g < n` and `p ∤ g.coeff 0`, the polynomial `Xⁿ + p·g` is
Eisenstein at `p`: monic of degree `n`, every lower coefficient is `p · g.coeff k`
(divisible by `p`), and the constant coefficient `p · g.coeff 0` is divisible by `p`
but not `p²`. This is the "arbitrary lower coefficients" generalization. -/

/-- `Xⁿ + p·g` is monic when `deg g < n`. -/
theorem monic_X_pow_add_CP_mul {p : ℤ} (hp : Prime p) {n : ℕ} {g : ℤ[X]}
    (hg : g.natDegree < n) : ((X : ℤ[X]) ^ n + C p * g).Monic := by
  apply monic_X_pow_add
  rw [degree_C_mul hp.ne_zero]
  exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hg)

/-- `Xⁿ + p·g` has degree exactly `n` when `0 < n` and `deg g < n`. -/
theorem natDegree_X_pow_add_CP_mul {p : ℤ} (hp : Prime p) {n : ℕ} {g : ℤ[X]}
    (hg : g.natDegree < n) : ((X : ℤ[X]) ^ n + C p * g).natDegree = n := by
  apply natDegree_eq_of_degree_eq_some
  have hlt : (C p * g).degree < ((X : ℤ[X]) ^ n).degree := by
    rw [degree_X_pow, degree_C_mul hp.ne_zero]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hg)
  rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]

/-- **The general Eisenstein family is irreducible over `ℤ`.**
For any `g` with `deg g < n` (`0 < n`) and `p ∤ g.coeff 0`, the monic polynomial
`Xⁿ + p·g` is irreducible. This realizes "Eisenstein-at-`p` with arbitrary lower
coefficients divisible by `p`". -/
theorem irreducible_int_X_pow_add_CP_mul {p : ℤ} (hp : Prime p) {n : ℕ} (hn : 0 < n)
    {g : ℤ[X]} (hg : g.natDegree < n) (hg0 : ¬ p ∣ g.coeff 0) :
    Irreducible ((X : ℤ[X]) ^ n + C p * g) := by
  have hmonic := monic_X_pow_add_CP_mul hp hg
  have hnd := natDegree_X_pow_add_CP_mul hp hg
  have hcoeff : ∀ k, ((X : ℤ[X]) ^ n + C p * g).coeff k
      = (if k = n then 1 else 0) + p * g.coeff k := by
    intro k; rw [coeff_add, coeff_X_pow, coeff_C_mul]
  refine irreducible_int_of_eisenstein hp hmonic (by rw [hnd]; exact hn) ?_ ?_
  · -- lower coefficients: `p · g.coeff k`, divisible by `p`
    intro k hk
    rw [hnd] at hk
    rw [hcoeff, if_neg (by omega : k ≠ n), zero_add]
    exact dvd_mul_right p (g.coeff k)
  · -- constant coefficient `p · g.coeff 0` is not divisible by `p²`
    rw [hcoeff, if_neg (by omega : (0 : ℕ) ≠ n), zero_add, pow_two]
    intro h
    exact hg0 ((mul_dvd_mul_iff_left hp.ne_zero).mp h)

/-- **The general Eisenstein family is irreducible over `ℚ`.** -/
theorem irreducible_rat_X_pow_add_CP_mul {p : ℤ} (hp : Prime p) {n : ℕ} (hn : 0 < n)
    {g : ℤ[X]} (hg : g.natDegree < n) (hg0 : ¬ p ∣ g.coeff 0) :
    Irreducible (((X : ℤ[X]) ^ n + C p * g).map (algebraMap ℤ ℚ)) :=
  ((monic_X_pow_add_CP_mul hp hg).irreducible_iff_irreducible_map_fraction_map).mp
    (irreducible_int_X_pow_add_CP_mul hp hn hg hg0)

/-! ### Recovering the parent family `Xⁿ − p`

`Xⁿ − p = Xⁿ + p·(−1)`, so it is the `g = −1` member of the family above. We obtain
irreducibility over `ℚ` as well, which is what gives `[ℚ(ⁿ√p) : ℚ] = n`. -/

/-- **`Xⁿ − p` is irreducible over `ℤ`**, recovered from the general family. -/
theorem irreducible_int_X_pow_sub_C {p : ℤ} (hp : Prime p) {n : ℕ} (hn : 0 < n) :
    Irreducible ((X : ℤ[X]) ^ n - C p) := by
  have heq : (X : ℤ[X]) ^ n - C p = X ^ n + C p * C (-1) := by
    rw [map_neg, map_one, mul_neg, mul_one, sub_eq_add_neg]
  rw [heq]
  refine irreducible_int_X_pow_add_CP_mul hp hn ?_ ?_
  · rw [natDegree_C]; exact hn
  · rw [coeff_C_zero]
    exact fun h => hp.not_unit (isUnit_of_dvd_unit h isUnit_one.neg)

/-- **`Xⁿ − p` is irreducible over `ℚ`** — the parent's flagship example, lifted to
the rationals (which is what underlies `[ℚ(ⁿ√p) : ℚ] = n`). -/
theorem irreducible_rat_X_pow_sub_C {p : ℤ} (hp : Prime p) {n : ℕ} (hn : 0 < n) :
    Irreducible (((X : ℤ[X]) ^ n - C p).map (algebraMap ℤ ℚ)) := by
  have hmonic : ((X : ℤ[X]) ^ n - C p).Monic := monic_X_pow_sub_C p hn.ne'
  exact (hmonic.irreducible_iff_irreducible_map_fraction_map).mp
    (irreducible_int_X_pow_sub_C hp hn)

/-! ### Concrete instances with genuinely nonzero lower coefficients

These are the cases the parent could *not* reach: Eisenstein polynomials whose
lower coefficients other than the constant term are nonzero. -/

/-- `X² + 2X + 2` is irreducible over `ℤ` (Eisenstein at `2`; the linear coefficient
`2` is a nonzero lower coefficient divisible by `2`). -/
theorem irreducible_int_X_sq_add_two_X_add_two :
    Irreducible ((X : ℤ[X]) ^ 2 + C 2 * X + C 2) := by
  have heq : (X : ℤ[X]) ^ 2 + C 2 * X + C 2 = X ^ 2 + C 2 * (X + C 1) := by
    rw [C_1]; ring
  rw [heq]
  refine irreducible_int_X_pow_add_CP_mul Int.prime_two (by norm_num) ?_ ?_
  · rw [natDegree_add_C, natDegree_X]; norm_num
  · rw [coeff_add, coeff_X_zero, coeff_C_zero]; norm_num

/-- `X³ + 3X + 3` is irreducible over `ℤ` (Eisenstein at `3`). -/
theorem irreducible_int_X_cube_add_three_X_add_three :
    Irreducible ((X : ℤ[X]) ^ 3 + C 3 * X + C 3) := by
  have heq : (X : ℤ[X]) ^ 3 + C 3 * X + C 3 = X ^ 3 + C 3 * (X + C 1) := by
    rw [C_1]; ring
  rw [heq]
  refine irreducible_int_X_pow_add_CP_mul Int.prime_three (by norm_num) ?_ ?_
  · rw [natDegree_add_C, natDegree_X]; norm_num
  · rw [coeff_add, coeff_X_zero, coeff_C_zero]; norm_num

/-- `X² + 2X + 2` is irreducible over `ℚ` — a concrete Eisenstein polynomial with a
nonzero middle coefficient, irreducible over the rationals. -/
theorem irreducible_rat_X_sq_add_two_X_add_two :
    Irreducible (((X : ℤ[X]) ^ 2 + C 2 * X + C 2).map (algebraMap ℤ ℚ)) := by
  have heq : (X : ℤ[X]) ^ 2 + C 2 * X + C 2 = X ^ 2 + C 2 * (X + C 1) := by
    rw [C_1]; ring
  rw [heq]
  refine irreducible_rat_X_pow_add_CP_mul Int.prime_two (by norm_num) ?_ ?_
  · rw [natDegree_add_C, natDegree_X]; norm_num
  · rw [coeff_add, coeff_X_zero, coeff_C_zero]; norm_num

end EisensteinCriterionOQ01OQ03
