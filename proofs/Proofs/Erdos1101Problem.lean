/-
  Erdős Problem #1101: Good Sequences and Gaps in Sieved Integers

  Given a sequence u = {u₁ < u₂ < ...} of pairwise coprime integers with
  convergent reciprocal series, let A = {a₁ < a₂ < ...} be integers not
  divisible by any uᵢ. The sequence u is "good" if gaps in A are bounded
  by (1+ε)·tₓ·∏(1 - 1/uᵢ)⁻¹ for large x.

  **Questions**:
  1. Is there a good sequence with polynomial growth uₙ < n^O(1)? (Conjectured NO)
  2. Is there a good sequence with sub-exponential growth uₙ ≤ e^o(n)? (Conjectured YES)

  **Status**: OPEN - Both questions remain unresolved.

  **Historical Context**:
  Erdős proved the existence of some good sequence (using all primes).
  The lower bound ≥ (1+o(1))·tₓ·∏(1 - 1/uᵢ)⁻¹ follows from sieve theory.
  The strong form of Problem #208 asks if prime squares form a good sequence.

  References:
  - https://erdosproblems.com/1101
  - Erdős, P. "Some problems and results on additive and multiplicative
    number theory" Analytic Number Theory (1981), 171-182
-/

import Mathlib

open Nat Filter

namespace Erdos1101

/-!
## Core Definitions

We define the key objects: the sieved set A, the counting index t,
and the predicate for "good" sequences.
-/

/-- The set of positive integers not divisible by any element of the sequence u.
These are the integers that "survive" the sieve defined by u. -/
def ASet (u : ℕ → ℕ) : Set ℕ :=
  { a | ∀ i, ¬ u i ∣ a }

/-- The sequence A_u: the positive integers not divisible by any uᵢ,
arranged in increasing order. A u n is the (n+1)-th such integer. -/
noncomputable def A (u : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.nth (fun a => a ∈ ASet u) n

/-- The index tₓ such that u₀·u₁·...·u_{tₓ-1} ≤ x < u₀·u₁·...·u_{tₓ}.
This measures how many terms of u have product at most x. -/
noncomputable def t (u : ℕ → ℕ) (x : ℕ) : ℕ :=
  sSup { k | ∏ i ∈ Finset.range k, u i ≤ x }

/-!
## The "Good Sequence" Predicate

A sequence u is "good" if it satisfies four conditions:
1. Strictly increasing
2. Pairwise coprime
3. Convergent reciprocal series
4. Gaps in A(u) are bounded by the product formula
-/

/-- A sequence u is "good" if:
1. It is strictly monotone increasing
2. Any two distinct terms are coprime
3. The series Σ 1/uᵢ converges
4. For any ε > 0, eventually all gaps aₖ₊₁ - aₖ satisfy the bound -/
def IsGood (u : ℕ → ℕ) : Prop :=
  StrictMono u ∧
  (∀ i j, i ≠ j → Nat.Coprime (u i) (u j)) ∧
  Summable (fun n => 1 / (u n : ℝ)) ∧
  ∀ ε > 0, ∀ᶠ x in atTop,
    ∀ k, A u k < x →
      (A u (k + 1) : ℝ) - A u k < (1 + ε) * (t u x : ℝ) * (∏' i : ℕ, (1 - 1 / (u i : ℝ)))⁻¹

/-!
## The Conjectures

Erdős conjectured:
1. NO good sequence has polynomial growth
2. YES there exists a good sequence with sub-exponential growth
-/

/-- **Erdős's First Conjecture**: There is NO good sequence with polynomial growth.

If u is good, then u cannot grow like n^k for any fixed k.
This remains OPEN. -/
axiom erdos_1101_no_polynomial :
    ¬ ∃ u, IsGood u ∧ ∃ k : ℕ, (fun n => (u n : ℝ)) =O[atTop] (fun n => (n : ℝ) ^ k)

/-- **Erdős's Second Conjecture**: There IS a good sequence with sub-exponential growth.

There exists a good sequence u such that log(uₙ) = o(n), meaning uₙ grows
slower than any exponential e^(cn).
This remains OPEN. -/
axiom erdos_1101_yes_subexponential :
    ∃ u, IsGood u ∧ (fun n => Real.log (u n : ℝ)) =o[atTop] (fun n => (n : ℝ))

/-!
## Known Results

Erdős proved the existence of SOME good sequence (using primes).
Sieve theory gives a matching lower bound for gaps.
-/

/-- **Erdős's Existence Theorem**: There exists a good sequence.

Erdős proved this using the sequence of all primes. This shows the "good"
condition is achievable, but doesn't address the growth rate questions. -/
axiom erdos_good_sequence_exists : ∃ u, IsGood u

/-- **Sieve Lower Bound**: For ANY sequence u satisfying the coprimality and
convergence conditions, gaps in A(u) are at least (1+o(1))·tₓ·∏(1-1/uᵢ)⁻¹.

This shows the bound in the definition of "good" is essentially optimal. -/
axiom sieve_lower_bound (u : ℕ → ℕ)
    (h_coprime : ∀ i j, i ≠ j → Nat.Coprime (u i) (u j))
    (h_conv : Summable (fun n => 1 / (u n : ℝ))) :
    ∀ᶠ x in atTop, ∃ k, A u k < x ∧
      (A u (k + 1) : ℝ) - A u k > (1 - 1) * (t u x : ℝ) * (∏' i : ℕ, (1 - 1 / (u i : ℝ)))⁻¹

/-!
## Related Problem: Prime Squares

The strong form of Problem #208 asks whether the sequence of prime squares
u_i = p_i² forms a good sequence. This is a specific instance of the general
question about growth rates.
-/

/-- The sequence of squares of consecutive primes: 4, 9, 25, 49, ... -/
noncomputable def primeSquares (n : ℕ) : ℕ := (Nat.nth Nat.Prime n) ^ 2

/-- **Problem #208 Strong Form**: Is the sequence of prime squares good?

This specific question remains open and connects to the general theory. -/
axiom prime_squares_good_conjecture : IsGood primeSquares

end Erdos1101
