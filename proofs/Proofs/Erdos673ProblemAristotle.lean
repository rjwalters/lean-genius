/-
  Aristotle targets for Erdős Problem #673
  Routine supporting lemmas for automated proof search.
  See Erdos673Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture or deep analytic results
  - Known results: sorted list properties, ratio bounds, concrete computations
  - Clean theorem statements with no definition sorries

  Excluded (deep/analytic results kept in main file):
  - tao_lower_bound (Tao's structural argument)
  - G_even_lower_bound (needs divisor structure analysis)
  - average_G_tends_to_infinity (asymptotic analysis)
  - first_question_trivial (density argument)
  - erdos_tenenbaum_distribution (deep analytic number theory)
  - G_coprime_relation (structural argument on coprime divisors)
  - sum_G_asymptotic (asymptotic formula)
  - highly_composite_G_large (needs analysis of highly composite numbers)
  - tau_sum_asymptotic (Dirichlet's theorem on average order of τ)
  - G_tau_similar_average (follows from deep results)
-/
import Mathlib

namespace Erdos673.Aristotle

open Nat Finset Real Filter

/- ## Sorted Divisor Definitions (mirrored from main file) -/

noncomputable def sortedDivisors (n : ℕ) : List ℕ :=
  (n.divisors.sort (· ≤ ·))

def tau (n : ℕ) : ℕ := n.divisors.card

noncomputable def divisorAt (n : ℕ) (i : ℕ) : ℕ :=
  (sortedDivisors n).getD i 0

noncomputable def G (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (tau n - 1),
    (divisorAt n i : ℝ) / (divisorAt n (i + 1) : ℝ)

/- ## Section 1: Basic Sorted Divisor Properties -/

-- First divisor of n ≥ 1 is always 1
theorem first_divisor_eq_one (n : ℕ) (hn : n ≥ 1) :
    divisorAt n 0 = 1 := by sorry

-- Last divisor of n ≥ 1 is n itself
theorem last_divisor_eq_n (n : ℕ) (hn : n ≥ 1) :
    divisorAt n (tau n - 1) = n := by sorry

/- ## Section 2: G for Specific Primes and Prime Powers -/

-- G(p) = 1/p: divisors of prime p are {1, p}, ratio = 1/p
theorem G_prime (p : ℕ) (hp : p.Prime) : G p = 1 / p := by sorry

-- G(p²) = 2/p: divisors {1, p, p²}, ratios 1/p + p/p² = 2/p
theorem G_prime_sq (p : ℕ) (hp : p.Prime) : G (p ^ 2) = 2 / p := by sorry

/- ## Section 3: Upper Bounds -/

-- Each consecutive divisor ratio dᵢ/dᵢ₊₁ ≤ 1, so G(n) ≤ τ(n) - 1
theorem G_upper_bound (n : ℕ) (hn : n ≥ 1) :
    G n ≤ tau n - 1 := by sorry

-- Tao's upper bound follows: G(n) ≤ τ(n)
theorem tao_upper_bound (n : ℕ) (hn : n ≥ 1) :
    G n ≤ tau n := by sorry

/- ## Section 4: GRatio Boundedness -/

noncomputable def GRatio (n : ℕ) : ℝ :=
  if tau n = 0 then 0 else G n / tau n

-- GRatio is in [0, 1] for n ≥ 1
theorem GRatio_bounded (n : ℕ) (hn : n ≥ 1) :
    0 ≤ GRatio n ∧ GRatio n ≤ 1 := by sorry

/- ## Section 5: Concrete Computations -/

-- G(6): divisors 1,2,3,6 → ratios 1/2, 2/3, 3/6
theorem G_6 : G 6 = 1/2 + 2/3 + 1/2 := by sorry

-- G(12): divisors 1,2,3,4,6,12 → ratios 1/2, 2/3, 3/4, 4/6, 6/12
theorem G_12 : G 12 = 1/2 + 2/3 + 3/4 + 4/6 + 6/12 := by sorry

/- ## Section 6: Non-Multiplicativity -/

-- G is not multiplicative: concrete counterexample witnesses
theorem G_not_multiplicative :
    ∃ a b : ℕ, Nat.Coprime a b ∧ a ≥ 2 ∧ b ≥ 2 ∧ G (a * b) ≠ G a * G b := by sorry

end Erdos673.Aristotle
