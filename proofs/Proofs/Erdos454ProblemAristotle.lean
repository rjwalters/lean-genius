/-
  Aristotle targets for Erdős Problem #454 (Prime Sum Deviations)
  Routine supporting lemmas and concrete examples for automated proof search.
  See Erdos454Problem.lean for the main formalization.

  The 3 sorries in the main file:

  1. gap_deviation_connection — proved directly below using large_prime_gaps_exist.
     The antecedent (∀ n, deviation n ≤ 0) is unused; the conclusion follows from
     the axiom that prime gaps are unbounded.

  2. example_f_3 — f(3) = 16.
     f 3 = min over 0 < i < 3 of (nthPrime(3+i) + nthPrime(3-i)) (i = 0 excluded):
       i=1: nthPrime 4 + nthPrime 2 = 11 + 5 = 16
       i=2: nthPrime 5 + nthPrime 1 = 13 + 3 = 16
     Proof strategy: rw [f_eq_f']; simp [f', nthPrime]

  3. example_deviation_3 — deviation(3) = f(3) - 2*nthPrime(3) = 16 - 14 = 2.
     Proof strategy: simp [deviation]; rw [show f 3 = 16 from example_f_3];
                     norm_num [show (nthPrime 3 : ℤ) = 7 from by simp [nthPrime]]

  NOT included:
  - Erdős #454 main conjecture (limsup deviationENat = ⊤) — open problem
  - pomerance_1979 bound — deep number theory axiom, not Aristotle-provable
-/
import Mathlib
import Proofs.Erdos454Problem

namespace Erdos454ProblemAristotle

open Erdos454 Nat Filter

-- Proved directly: prime gaps are unbounded (the antecedent is unused).
-- The conclusion follows from large_prime_gaps_exist: for any G, ∃ k with gap ≥ G.
theorem gap_deviation_connection :
    (∀ n, deviation n ≤ 0) → ¬∃ G : ℕ, G > 0 ∧ ∀ k, nthPrime (k + 1) - nthPrime k < G := by
  intro _
  rintro ⟨G, hG, hbnd⟩
  obtain ⟨k, hk⟩ := large_prime_gaps_exist G
  exact absurd (hbnd k) (by omega)

-- nth_prime_five_eq_thirteen is not in Mathlib (only up to nth_prime_four_eq_eleven),
-- so derive it locally from primality of 13 and count Nat.Prime 13 = 5.
@[simp]
theorem nth_prime_five_eq_thirteen : nth Nat.Prime 5 = 13 := by
  have h13 : Nat.Prime 13 := by decide
  have hc : Nat.count Nat.Prime 13 = 5 := by decide
  simpa [hc] using Nat.nth_count h13

-- Target for Aristotle: f(3) = 16 (concrete Finset.inf' computation, i = 0 excluded).
theorem example_f_3 : f 3 = 16 := by
  rw [f_eq_f']
  simp [f', nthPrime, Finset.range_add_one, Finset.range_zero,
    Finset.inf'_insert, Finset.inf'_singleton]

-- Target for Aristotle: deviation(3) = 2 (follows from f(3) = 16 and nthPrime(3) = 7).
theorem example_deviation_3 : deviation 3 = 2 := by
  simp only [deviation, example_f_3]
  norm_num [nthPrime, show nthPrime 3 = 7 from by simp [nthPrime]]

end Erdos454ProblemAristotle
