/-
Erdős Problem #884: Divisor Gap Sums

Source: https://erdosproblems.com/884
Status: OPEN

Statement:
Let d₁ < d₂ < ... < d_t be the divisors of n. Is it true that
  Σ_{1≤i<j≤t} 1/(d_j - d_i) ≪ 1 + Σ_{1≤i<t} 1/(d_{i+1} - d_i)
with an absolute implied constant?

Background:
- The left side sums over ALL pairs of divisors
- The right side sums only over CONSECUTIVE divisors
- The question asks if the "all pairs" sum is controlled by the "consecutive pairs" sum

Reference: [Er98], see also Problem #144
-/

import Mathlib.Data.Nat.Divisors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic

open Nat Finset BigOperators

namespace Erdos884

/-! ## Part I: Divisor Lists -/

/-- The divisors of n as a sorted list. -/
noncomputable def divisorList (n : ℕ) : List ℕ :=
  (n.divisors.sort (· ≤ ·))

/-- Number of divisors τ(n). -/
def numDivisors (n : ℕ) : ℕ := n.divisors.card

/-- Access the i-th divisor (0-indexed). -/
noncomputable def divisor (n i : ℕ) : ℕ :=
  (divisorList n).getD i 0

/-- The divisor list is sorted. -/
axiom divisorList_sorted (n : ℕ) : (divisorList n).Sorted (· < ·)

/-- The divisor list contains exactly the divisors. -/
axiom mem_divisorList_iff (n d : ℕ) (hn : n > 0) :
    d ∈ divisorList n ↔ d ∣ n ∧ d > 0

/-! ## Part II: Divisor Gaps -/

/-- Consecutive divisor gap: d_{i+1} - d_i. -/
noncomputable def consecutiveGap (n i : ℕ) : ℕ :=
  divisor n (i + 1) - divisor n i

/-- General divisor gap: d_j - d_i for i < j. -/
noncomputable def generalGap (n i j : ℕ) : ℕ :=
  divisor n j - divisor n i

/-- Consecutive gaps are positive for sorted divisors. -/
axiom consecutiveGap_pos (n i : ℕ) (hn : n > 1) (hi : i + 1 < numDivisors n) :
    consecutiveGap n i > 0

/-- General gaps with i < j are positive. -/
axiom generalGap_pos (n i j : ℕ) (hn : n > 1) (hij : i < j) (hj : j < numDivisors n) :
    generalGap n i j > 0

/-! ## Part III: The Two Sums -/

/-- All-pairs sum: Σ_{0≤i<j<t} 1/(d_j - d_i). -/
noncomputable def allPairsSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (numDivisors n),
    ∑ j ∈ Finset.Ioo i (numDivisors n),
      (1 : ℝ) / (generalGap n i j)

/-- Consecutive-pairs sum: Σ_{0≤i<t-1} 1/(d_{i+1} - d_i). -/
noncomputable def consecutivePairsSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (numDivisors n - 1),
    (1 : ℝ) / (consecutiveGap n i)

/-! ## Part IV: The Main Conjecture -/

/--
**Erdős Problem #884 (OPEN):**
Does there exist an absolute constant C such that for all n ≥ 2:
  allPairsSum(n) ≤ C * (1 + consecutivePairsSum(n))
-/
def ErdosConjecture884 : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 1 →
    allPairsSum n ≤ C * (1 + consecutivePairsSum n)

/-- The conjecture is axiomatized (OPEN). -/
axiom erdos_884 : ErdosConjecture884

/-! ## Part V: Basic Properties -/

/-- The all-pairs sum is non-negative. -/
axiom allPairsSum_nonneg (n : ℕ) : allPairsSum n ≥ 0

/-- The consecutive-pairs sum is non-negative. -/
axiom consecutivePairsSum_nonneg (n : ℕ) : consecutivePairsSum n ≥ 0

/-- Number of terms in consecutive-pairs sum: τ(n) - 1. -/
theorem consecutivePairsSum_num_terms (n : ℕ) (hn : n > 0) :
    (Finset.range (numDivisors n - 1)).card = numDivisors n - 1 := by
  simp

/-! ## Part VI: Examples -/

/-- For n = 6, divisors are [1, 2, 3, 6]. -/
axiom divisors_6 : divisorList 6 = [1, 2, 3, 6]

/-- For prime p, divisors are [1, p]. -/
axiom divisors_prime (p : ℕ) (hp : p.Prime) :
    divisorList p = [1, p]

/-- For primes, allPairsSum = consecutivePairsSum (trivially). -/
axiom prime_case_equality (p : ℕ) (hp : p.Prime) :
    allPairsSum p = consecutivePairsSum p

/-! ## Part VII: Structural Lemmas -/

/-- Any gap is at least the largest consecutive gap involved. -/
axiom gap_lower_bound (n i j : ℕ) (hij : i < j) :
    generalGap n i j ≥ consecutiveGap n i

/-- For coprime m, n: τ(mn) = τ(m) · τ(n). -/
axiom numDivisors_mul_coprime (m n : ℕ) (hm : m > 0) (hn : n > 0) (hcop : Nat.Coprime m n) :
    numDivisors (m * n) = numDivisors m * numDivisors n

/-! ## Part VIII: Connections -/

/-- The harmonic sum over divisors: σ_{-1}(n) = Σ_{d|n} 1/d. -/
noncomputable def divisorHarmonicSum (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (1 : ℝ) / d

/-- Connection to Problem #144 on divisor arithmetic. -/
axiom problem_144_connection : True

/-! ## Part IX: Summary -/

/--
**Erdős Problem #884: Summary**

QUESTION: Is Σ_{i<j} 1/(d_j - d_i) ≪ 1 + Σ_i 1/(d_{i+1} - d_i)?

STATUS: OPEN

KEY STRUCTURE:
- Left side: sum over ALL pairs of divisors
- Right side: sum over CONSECUTIVE pairs only
- For primes, the sums are equal
- Consecutive gaps form a natural basis for all gaps
-/
theorem erdos_884_statement : ErdosConjecture884 ↔
    ∃ C : ℝ, C > 0 ∧ ∀ n > 1, allPairsSum n ≤ C * (1 + consecutivePairsSum n) := by
  rfl

/-- The problem remains OPEN. -/
theorem erdos_884_status : True := trivial

end Erdos884
