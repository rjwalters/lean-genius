/-
  Aristotle targets for Erdos1196Problem
  Routine supporting lemmas for automated proof search.
  See Erdos1196Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjectures or deep analytic results (axiomatized separately)
  - Routine algebraic/sum manipulations that follow from standard Mathlib lemmas
  - No definition sorries
  - No axioms

  Included targets (2):
  - vonMangoldt_sum_eq_log_comp: ∑ d in filter (· ∣ n) (range (n+1)), Λ d = log n
    (restatement of Mathlib's vonMangoldt_sum using the filter form)
  - transition_sum_eq_one_comp: transition probabilities sum to 1
    (follows from vonMangoldt_sum_eq_log_comp by division by log n)
-/
import Mathlib

open Real Nat ArithmeticFunction

namespace Erdos1196Aristotle

/-- The transition probability from n to n/q in the downward divisibility chain. -/
noncomputable def transitionProb (n q : ℕ) : ℝ :=
  if q ∣ n ∧ 2 ≤ n then (vonMangoldt q : ℝ) / log (n : ℝ) else 0

-- Routine: the von Mangoldt sum over divisors of n equals log n.
-- Follows from Mathlib's vonMangoldt_sum (which uses n.divisors) by showing
-- filter (· ∣ n) (range (n+1)) = n.divisors for n ≥ 1 (since 0 ∤ n for n ≥ 2).
theorem vonMangoldt_sum_eq_log_comp (n : ℕ) (hn : 2 ≤ n) :
    (Finset.filter (· ∣ n) (Finset.range (n + 1))).sum
      (fun d => (vonMangoldt d : ℝ)) = log (n : ℝ) := by
  sorry

-- Routine: the transition probabilities from state n sum to 1.
-- The sum ∑_{q | n} (Λ(q) / log n) = (∑_{q | n} Λ(q)) / log n = log n / log n = 1.
theorem transition_sum_eq_one_comp (n : ℕ) (hn : 2 ≤ n) :
    (Finset.filter (· ∣ n) (Finset.range (n + 1))).sum
      (fun q => transitionProb n q) = 1 := by
  sorry

end Erdos1196Aristotle
