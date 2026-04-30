/-
  Aristotle targets for Erdős Problem #454 (Prime Sum Deviations)
  Routine supporting lemmas and concrete examples for automated proof search.
  See Erdos454Problem.lean for the main formalization.

  The 3 sorries in the main file:

  1. gap_deviation_connection — proved directly below using large_prime_gaps_exist.
     The antecedent (∀ n, deviation n ≤ 0) is unused; the conclusion follows from
     the axiom that prime gaps are unbounded.

  2. example_f_3 — f(3) = 14.
     f 3 = min over i < 3 of (nthPrime(3+i) + nthPrime(3-i)):
       i=0: nthPrime 3 + nthPrime 3 = 7 + 7 = 14  ← minimum
       i=1: nthPrime 4 + nthPrime 2 = 11 + 5 = 16
       i=2: nthPrime 5 + nthPrime 1 = 13 + 3 = 16
     Proof strategy: rw [f_eq_f']; simp [f', nthPrime]; native_decide

  3. example_deviation_3 — deviation(3) = f(3) - 2*nthPrime(3) = 14 - 14 = 0.
     Proof strategy: simp [deviation]; rw [show f 3 = 14 from example_f_3];
                     norm_num [show (nthPrime 3 : ℤ) = 7 from by simp [nthPrime]; native_decide]

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

-- Target for Aristotle: f(3) = 14 (concrete Finset.inf' computation).
theorem example_f_3 : f 3 = 14 := by
  sorry

-- Target for Aristotle: deviation(3) = 0 (follows from f(3) = 14 and nthPrime(3) = 7).
theorem example_deviation_3 : deviation 3 = 0 := by
  sorry

end Erdos454ProblemAristotle
