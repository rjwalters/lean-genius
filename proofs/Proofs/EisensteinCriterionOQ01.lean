/-
  Eisenstein's irreducibility criterion, and the irreducibility of `Xⁿ − p`.

  **Eisenstein's criterion.**  Let `R` be an integral domain, `P ⊂ R` a prime
  ideal, and `f ∈ R[X]` a primitive polynomial of positive degree whose

    * leading coefficient lies OUTSIDE `P`,
    * all lower coefficients lie IN `P`,
    * constant coefficient lies OUTSIDE `P²`.

  Then `f` is irreducible.

  The flagship consequence over `ℤ`: for every prime `p` and every `n ≥ 1` the
  polynomial `Xⁿ − p` is irreducible.  Taking `P = (p)` the Eisenstein
  hypotheses read off the coefficients `1, 0, …, 0, −p`:

    * leading coefficient `1 ∉ (p)`        (else `p ∣ 1`, impossible),
    * the only nonzero lower coefficient is `−p ∈ (p)`,
    * the constant coefficient `−p ∉ (p²)`  (else `p² ∣ p`, i.e. `p ∣ 1`).

  In particular `X² − 2`, `X³ − 2`, `X⁵ − 3`, … are all irreducible over `ℤ`,
  so `ⁿ√p` has minimal polynomial of degree `n` — the standard supply of
  algebraic numbers of every degree.

  Mathlib provides the general criterion as
  `Polynomial.irreducible_of_eisenstein_criterion`; this file restates it and
  carries out the concrete coefficient bookkeeping for the `Xⁿ − p` family.
  Everything is fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open Polynomial

namespace EisensteinCriterionOQ01

/-! ### Eisenstein's criterion (general form) -/

/-- **Eisenstein's irreducibility criterion.** A primitive polynomial `f` of
positive degree over an integral domain, with leading coefficient outside a
prime ideal `P`, all lower coefficients inside `P`, and constant coefficient
outside `P²`, is irreducible. -/
theorem irreducible_of_eisenstein {R : Type*} [CommRing R] [IsDomain R]
    {f : R[X]} {P : Ideal R} (hP : P.IsPrime)
    (hlead : f.leadingCoeff ∉ P)
    (hlow : ∀ k : ℕ, (k : WithBot ℕ) < f.degree → f.coeff k ∈ P)
    (hdeg : 0 < f.degree)
    (hconst : f.coeff 0 ∉ P ^ 2)
    (hprim : f.IsPrimitive) : Irreducible f :=
  irreducible_of_eisenstein_criterion hP hlead hlow hdeg hconst hprim

/-! ### The Eisenstein polynomials `Xⁿ − p` over ℤ -/

/-- **`Xⁿ − p` is irreducible over `ℤ`** for every prime `p` and every `n ≥ 1`.
The canonical Eisenstein family: applying the criterion with `P = (p)`. -/
theorem irreducible_X_pow_sub_C_prime {p : ℤ} (hp : Prime p) {n : ℕ} (hn : 0 < n) :
    Irreducible ((X : ℤ[X]) ^ n - C p) := by
  have hP : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hmonic : ((X : ℤ[X]) ^ n - C p).Monic := monic_X_pow_sub_C p hn.ne'
  have hdeg : ((X : ℤ[X]) ^ n - C p).degree = (n : WithBot ℕ) := degree_X_pow_sub_C hn p
  -- coefficient bookkeeping: coeff k = (if k = n then 1 else 0) − (if k = 0 then p else 0)
  have hcoeff : ∀ k : ℕ, ((X : ℤ[X]) ^ n - C p).coeff k
      = (if k = n then 1 else 0) - (if k = 0 then p else 0) := by
    intro k
    rw [coeff_sub, coeff_X_pow, coeff_C]
  refine irreducible_of_eisenstein hP ?_ ?_ ?_ ?_ hmonic.isPrimitive
  · -- leading coefficient 1 ∉ (p)
    rw [hmonic.leadingCoeff, Ideal.mem_span_singleton]
    exact fun h => hp.not_unit (isUnit_of_dvd_one h)
  · -- every lower coefficient lies in (p)
    intro k hk
    rw [hdeg] at hk
    have hkn : k < n := by exact_mod_cast hk
    rw [Ideal.mem_span_singleton, hcoeff, if_neg (by omega : k ≠ n)]
    by_cases hk0 : k = 0
    · simp [hk0]
    · simp [hk0]
  · -- positive degree
    rw [hdeg]; exact_mod_cast hn
  · -- constant coefficient −p ∉ (p²)
    rw [hcoeff, if_neg (by omega : (0 : ℕ) ≠ n), if_pos rfl,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [zero_sub, dvd_neg]
    intro h
    -- p² ∣ p forces p ∣ 1
    have : p * p ∣ p * 1 := by rwa [mul_one, ← sq]
    exact hp.not_unit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hp.ne_zero).mp this))

/-! ### Concrete instances -/

/-- `X² − 2` is irreducible over `ℤ`. -/
theorem irreducible_X_sq_sub_two : Irreducible ((X : ℤ[X]) ^ 2 - C 2) :=
  irreducible_X_pow_sub_C_prime Int.prime_two (by norm_num)

/-- `X³ − 2` is irreducible over `ℤ`. -/
theorem irreducible_X_cube_sub_two : Irreducible ((X : ℤ[X]) ^ 3 - C 2) :=
  irreducible_X_pow_sub_C_prime Int.prime_two (by norm_num)

/-- `X⁵ − 3` is irreducible over `ℤ`. -/
theorem irreducible_X_pow_five_sub_three : Irreducible ((X : ℤ[X]) ^ 5 - C 3) :=
  irreducible_X_pow_sub_C_prime Int.prime_three (by norm_num)

end EisensteinCriterionOQ01
