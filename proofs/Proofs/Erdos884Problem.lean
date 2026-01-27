/-
Erdős Problem #884: Divisor Gap Sums

Source: https://erdosproblems.com/884
Status: OPEN
Reference: Erdős [Er98], related to Problem #144

Statement:
Let d₁ < d₂ < ... < d_t be the divisors of n. Is it true that
  Σ_{1≤i<j≤t} 1/(d_j - d_i) ≪ 1 + Σ_{1≤i<t} 1/(d_{i+1} - d_i)
with an absolute implied constant?

The left side sums over ALL pairs of divisors; the right side sums only over
CONSECUTIVE divisors. The question asks whether the all-pairs sum is controlled
by the consecutive-pairs sum (plus 1) up to a universal constant.

Terence Tao has indicated this problem appears tractable.
-/

import Mathlib.Data.Nat.Divisors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Sort

open Nat Finset BigOperators

namespace Erdos884

/-!
# Erdős Problem 884: Divisor Gap Sums

*Reference:* [erdosproblems.com/884](https://www.erdosproblems.com/884)

For a positive integer n with divisors d₁ < d₂ < ··· < d_t, this problem asks whether
the sum over all pairs 1/(d_j - d_i) is bounded by an absolute constant times
(1 + sum over consecutive pairs 1/(d_{i+1} - d_i)).
-/

/-! ## Divisor Lists -/

/-- The divisors of n as a sorted list. -/
noncomputable def divisorList (n : ℕ) : List ℕ :=
  (n.divisors.sort (· ≤ ·))

/-- Number of divisors τ(n). -/
def numDivisors (n : ℕ) : ℕ := n.divisors.card

/-- Access the i-th divisor (0-indexed). -/
noncomputable def divisor (n i : ℕ) : ℕ :=
  (divisorList n).getD i 0

/-- The divisor list is strictly sorted. -/
axiom divisorList_sorted (n : ℕ) : (divisorList n).Sorted (· < ·)

/-- The divisor list contains exactly the positive divisors. -/
axiom mem_divisorList_iff (n d : ℕ) (hn : n > 0) :
    d ∈ divisorList n ↔ d ∣ n ∧ d > 0

/-! ## Divisor Gaps -/

/-- Consecutive divisor gap: d_{i+1} - d_i. -/
noncomputable def consecutiveGap (n i : ℕ) : ℕ :=
  divisor n (i + 1) - divisor n i

/-- General divisor gap: d_j - d_i for any pair. -/
noncomputable def generalGap (n i j : ℕ) : ℕ :=
  divisor n j - divisor n i

/-- Consecutive gaps are positive for sorted divisors. -/
axiom consecutiveGap_pos (n i : ℕ) (hn : n > 1) (hi : i + 1 < numDivisors n) :
    consecutiveGap n i > 0

/-- General gaps with i < j are positive. -/
axiom generalGap_pos (n i j : ℕ) (hn : n > 1) (hij : i < j) (hj : j < numDivisors n) :
    generalGap n i j > 0

/-! ## The Two Sums -/

/-- All-pairs sum: Σ_{0≤i<j<t} 1/(d_j - d_i).
    This sums over all C(τ(n), 2) pairs of divisors. -/
noncomputable def allPairsSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (numDivisors n),
    ∑ j ∈ Finset.Ioo i (numDivisors n),
      (1 : ℝ) / (generalGap n i j)

/-- Consecutive-pairs sum: Σ_{0≤i<t-1} 1/(d_{i+1} - d_i).
    This sums over the τ(n) - 1 consecutive gaps. -/
noncomputable def consecutivePairsSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (numDivisors n - 1),
    (1 : ℝ) / (consecutiveGap n i)

/-! ## The Main Conjecture -/

/-- Erdős Problem #884 (OPEN):
    Does there exist an absolute constant C such that for all n ≥ 2,
    allPairsSum(n) ≤ C · (1 + consecutivePairsSum(n))? -/
def ErdosConjecture884 : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 1 →
    allPairsSum n ≤ C * (1 + consecutivePairsSum n)

/-- The conjecture is axiomatized as the problem is OPEN. -/
axiom erdos_884 : ErdosConjecture884

/-! ## Basic Properties -/

/-- The all-pairs sum is non-negative. -/
axiom allPairsSum_nonneg (n : ℕ) : allPairsSum n ≥ 0

/-- The consecutive-pairs sum is non-negative. -/
axiom consecutivePairsSum_nonneg (n : ℕ) : consecutivePairsSum n ≥ 0

/-- Number of terms in consecutive-pairs sum: τ(n) - 1. -/
theorem consecutivePairsSum_num_terms (n : ℕ) (hn : n > 0) :
    (Finset.range (numDivisors n - 1)).card = numDivisors n - 1 := by
  simp

/-! ## Examples -/

/-- For n = 6, divisors are [1, 2, 3, 6]. -/
axiom divisors_6 : divisorList 6 = [1, 2, 3, 6]

/-- For prime p, divisors are [1, p]. -/
axiom divisors_prime (p : ℕ) (hp : p.Prime) :
    divisorList p = [1, p]

/-- For primes, allPairsSum = consecutivePairsSum (trivially: only one pair). -/
axiom prime_case_equality (p : ℕ) (hp : p.Prime) :
    allPairsSum p = consecutivePairsSum p

/-! ## Structural Lemmas -/

/-- Any general gap is at least the first consecutive gap involved.
    d_j - d_i ≥ d_{i+1} - d_i since divisors are increasing. -/
axiom gap_lower_bound (n i j : ℕ) (hij : i < j) :
    generalGap n i j ≥ consecutiveGap n i

/-- For coprime m, n: τ(mn) = τ(m) · τ(n).
    This multiplicativity of the divisor count affects gap patterns. -/
axiom numDivisors_mul_coprime (m n : ℕ) (hm : m > 0) (hn : n > 0)
    (hcop : Nat.Coprime m n) :
    numDivisors (m * n) = numDivisors m * numDivisors n

/-! ## Connections -/

/-- The harmonic sum over divisors: σ_{-1}(n) = Σ_{d|n} 1/d. -/
noncomputable def divisorHarmonicSum (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (1 : ℝ) / d

/-- The conjecture statement matches the informal problem. -/
theorem erdos_884_statement : ErdosConjecture884 ↔
    ∃ C : ℝ, C > 0 ∧ ∀ n > 1, allPairsSum n ≤ C * (1 + consecutivePairsSum n) := by
  rfl

end Erdos884
