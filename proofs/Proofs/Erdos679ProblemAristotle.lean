/-
  Aristotle targets for Erdős Problem #679: Small ω(n-k) for All k < n
  Routine supporting lemmas for automated proof search.
  See Erdos679Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the deep analytic number theory results (hardy_ramanujan, stronger_version_false,
    dottedcalculator_result, max_omega_bound, small_omega_density, density_upper_bound)
  - NOT the existence lower bounds (power_of_two_case, existence_of_large_omega)
  - NOT the open dichotomy conjecture
  - Factored sub-lemmas for omega_primorial (structural induction steps)
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings
-/
import Proofs.Erdos679Problem
import Mathlib

namespace Erdos679Aristotle

open Erdos679

/-
## Section 1: Primorial Structural Lemmas

The primorial of r is defined as the product of the first r primes (0-indexed).
These structural lemmas expose the inductive structure for Aristotle.
-/

/-- The primorial of 0 is 1 (empty product). -/
theorem primorial_zero_ari : primorial 0 = 1 := by
  simp [primorial]

/-- The primorial of r+1 equals (r-th prime) times primorial r. -/
theorem primorial_succ_ari (r : ℕ) :
    primorial (r + 1) = (Nat.nth Nat.Prime r) * primorial r := by
  unfold primorial
  rw [Finset.range_succ, Finset.prod_insert Finset.not_mem_range_self]

/-- omega(primorial 0) = 0, since primorial 0 = 1. -/
theorem omega_primorial_zero_ari : omega (primorial 0) = 0 := by
  rw [primorial_zero_ari]
  simp [omega]

/-
## Section 2: Nth Prime Lemmas

Basic facts about Nat.nth Nat.Prime used in the primorial induction.
-/

/-- Each element in the sequence Nat.nth Nat.Prime i is prime. -/
theorem nth_prime_is_prime_ari (i : ℕ) : Nat.Prime (Nat.nth Nat.Prime i) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i

/-- omega of the i-th prime equals 1. -/
theorem omega_nth_prime_ari (i : ℕ) : omega (Nat.nth Nat.Prime i) = 1 :=
  omega_prime _ (nth_prime_is_prime_ari i)

/-- The sequence Nat.nth Nat.Prime is strictly monotone. -/
theorem nth_prime_strictMono_ari : StrictMono (Nat.nth Nat.Prime) :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

/-- Distinct indices give distinct primes in the nth prime sequence. -/
theorem nth_prime_injective_ari : Function.Injective (Nat.nth Nat.Prime) :=
  nth_prime_strictMono_ari.injective

/-
## Section 3: Coprimality of nth Prime with Earlier Primorials

This is the key structural lemma: the r-th prime is coprime with primorial r.
It holds because the r-th prime is strictly larger than all primes in primorial r
(which are the 0th through (r-1)-th primes).
-/

/-- The r-th prime is coprime with primorial r.

    Proof: `Nat.nth Nat.Prime r` is prime, so coprimality reduces to non-divisibility
    of the product `∏ i < r, Nat.nth Nat.Prime i`. If it divided the product it would
    divide some factor `Nat.nth Nat.Prime i` with `i < r`; two primes dividing one
    another are equal, forcing `r = i` by injectivity of `Nat.nth Nat.Prime`,
    contradicting `i < r`. Mirrors the coprimality step inside `omega_primorial`. -/
theorem nth_prime_coprime_primorial_ari (r : ℕ) :
    Nat.Coprime (Nat.nth Nat.Prime r) (primorial r) := by
  have hp : (Nat.nth Nat.Prime r).Prime := nth_prime_is_prime_ari r
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  simp only [primorial] at hdvd
  obtain ⟨i, hi, hdvd_i⟩ := hp.prime.exists_mem_finset_dvd hdvd
  have hpi : (Nat.nth Nat.Prime i).Prime := nth_prime_is_prime_ari i
  have heq : Nat.nth Nat.Prime r = Nat.nth Nat.Prime i :=
    (Nat.prime_dvd_prime_iff_eq hp hpi).mp hdvd_i
  have hni : r = i := Nat.nth_injective Nat.infinite_setOf_prime heq
  rw [Finset.mem_range] at hi
  omega

/-
## Section 4: The omega_primorial Inductive Proof

Using the factored sub-lemmas to prove omega(primorial r) = r by induction.
Each step follows from coprimality and the sub-lemmas above.
-/

/-- omega(primorial r) = r, proved by structural induction. -/
theorem omega_primorial_ari (r : ℕ) : omega (primorial r) = r := by
  induction r with
  | zero => exact omega_primorial_zero_ari
  | succ r ih =>
    rw [primorial_succ_ari,
        omega_mul_coprime _ _ (nth_prime_coprime_primorial_ari r),
        omega_nth_prime_ari, ih]
    omega

end Erdos679Aristotle
