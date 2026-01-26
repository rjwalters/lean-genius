/-
Erdős Problem #884: Divisor Gap Sums

**Problem Statement (OPEN)**

Let d₁ < d₂ < ... < d_t be the divisors of n. Is it true that

  Σ_{1≤i<j≤t} 1/(d_j - d_i) ≪ 1 + Σ_{1≤i<t} 1/(d_{i+1} - d_i)

with an absolute implied constant?

**Background:**
- The left side sums over ALL pairs of divisors
- The right side sums only over CONSECUTIVE divisors
- The question asks if the "all pairs" sum is controlled by the "consecutive pairs" sum

**Status:** OPEN

**Reference:** [Er98], see also Problem #144

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Nat Finset BigOperators

namespace Erdos884

/-!
# Part 1: Divisor Lists

The ordered sequence of divisors of n.
-/

/-- The divisors of n as a sorted list. -/
noncomputable def divisorList (n : ℕ) : List ℕ :=
  (n.divisors.sort (· ≤ ·))

/-- Number of divisors τ(n). -/
def numDivisors (n : ℕ) : ℕ := n.divisors.card

/-- Access the i-th divisor (0-indexed). -/
noncomputable def divisor (n i : ℕ) : ℕ :=
  (divisorList n).getD i 0

/-- The divisor list is sorted. -/
theorem divisorList_sorted (n : ℕ) : (divisorList n).Sorted (· < ·) := by
  sorry

/-- The divisor list contains exactly the divisors. -/
theorem mem_divisorList_iff (n d : ℕ) (hn : n > 0) :
    d ∈ divisorList n ↔ d ∣ n ∧ d > 0 := by
  sorry

/-!
# Part 2: Divisor Gaps

The differences between consecutive divisors.
-/

/--
**Consecutive Divisor Gap**

For 0 ≤ i < t-1, the gap d_{i+1} - d_i between consecutive divisors.
-/
noncomputable def consecutiveGap (n i : ℕ) : ℕ :=
  divisor n (i + 1) - divisor n i

/--
**General Divisor Gap**

For i < j, the gap d_j - d_i between any two divisors.
-/
noncomputable def generalGap (n i j : ℕ) : ℕ :=
  divisor n j - divisor n i

/-- Consecutive gaps are positive. -/
theorem consecutiveGap_pos (n i : ℕ) (hn : n > 1) (hi : i + 1 < numDivisors n) :
    consecutiveGap n i > 0 := by
  sorry

/-- General gaps with i < j are positive. -/
theorem generalGap_pos (n i j : ℕ) (hn : n > 1) (hij : i < j) (hj : j < numDivisors n) :
    generalGap n i j > 0 := by
  sorry

/-!
# Part 3: The Two Sums

The main objects: sum over all pairs vs sum over consecutive pairs.
-/

/--
**All-Pairs Sum**

Σ_{0≤i<j<t} 1/(d_j - d_i) - sum over all pairs of divisors.
-/
noncomputable def allPairsSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (numDivisors n),
    ∑ j ∈ Finset.Ioo i (numDivisors n),
      (1 : ℝ) / (generalGap n i j)

/--
**Consecutive-Pairs Sum**

Σ_{0≤i<t-1} 1/(d_{i+1} - d_i) - sum over consecutive pairs only.
-/
noncomputable def consecutivePairsSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (numDivisors n - 1),
    (1 : ℝ) / (consecutiveGap n i)

/-!
# Part 4: The Main Conjecture

The all-pairs sum is controlled by the consecutive-pairs sum.
-/

/--
**Erdős Problem #884 (OPEN)**

Does there exist an absolute constant C such that for all n ≥ 2:

  allPairsSum(n) ≤ C * (1 + consecutivePairsSum(n))
-/
def ErdosConjecture884 : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 1 →
    allPairsSum n ≤ C * (1 + consecutivePairsSum n)

/-- Axiom for the open problem. -/
axiom erdos_884 : ErdosConjecture884

/-!
# Part 5: Basic Properties

Understanding the structure of the sums.
-/

/-- The all-pairs sum is non-negative. -/
theorem allPairsSum_nonneg (n : ℕ) : allPairsSum n ≥ 0 := by
  sorry

/-- The consecutive-pairs sum is non-negative. -/
theorem consecutivePairsSum_nonneg (n : ℕ) : consecutivePairsSum n ≥ 0 := by
  sorry

/-- Number of terms in all-pairs sum: τ(n) choose 2. -/
theorem allPairsSum_num_terms (n : ℕ) (hn : n > 0) :
    (Finset.filter (fun p => p.1 < p.2) (Finset.range (numDivisors n) ×ˢ Finset.range (numDivisors n))).card =
    numDivisors n * (numDivisors n - 1) / 2 := by
  sorry

/-- Number of terms in consecutive-pairs sum: τ(n) - 1. -/
theorem consecutivePairsSum_num_terms (n : ℕ) (hn : n > 0) :
    (Finset.range (numDivisors n - 1)).card = numDivisors n - 1 := by
  simp

/-!
# Part 6: Examples

Concrete computations for small n.
-/

/-- For n = 6, divisors are [1, 2, 3, 6]. -/
axiom divisors_6 : divisorList 6 = [1, 2, 3, 6]

/-- τ(6) = 4. -/
axiom numDivisors_6 : numDivisors 6 = 4

/--
**Example: n = 6**

Divisors: 1, 2, 3, 6

Consecutive gaps: 2-1=1, 3-2=1, 6-3=3
Consecutive sum: 1/1 + 1/1 + 1/3 = 2.333...

All gaps: (2-1, 3-1, 6-1, 3-2, 6-2, 6-3) = (1, 2, 5, 1, 4, 3)
All-pairs sum: 1/1 + 1/2 + 1/5 + 1/1 + 1/4 + 1/3 = 3.283...

Ratio: 3.283 / 3.333 ≈ 0.985
-/
axiom example_6 :
    let consSum := (1 : ℝ) + 1 + 1/3
    let allSum := 1 + 1/2 + 1/5 + 1 + 1/4 + 1/3
    allSum < 2 * (1 + consSum)

/-- For prime p, divisors are [1, p]. -/
axiom divisors_prime (p : ℕ) (hp : p.Prime) :
    divisorList p = [1, p]

/--
**Example: Prime p**

Divisors: 1, p

Consecutive sum: 1/(p-1)
All-pairs sum: 1/(p-1)

Equal! The conjecture holds trivially for primes.
-/
theorem prime_case_equality (p : ℕ) (hp : p.Prime) :
    allPairsSum p = consecutivePairsSum p := by
  sorry

/-!
# Part 7: Why This Might Be True

Intuition for the conjecture.
-/

/--
**Telescoping Intuition**

For j > i+1, we have:
  d_j - d_i = (d_j - d_{j-1}) + (d_{j-1} - d_{j-2}) + ... + (d_{i+1} - d_i)

So each 1/(d_j - d_i) is "smaller" than consecutive terms combined.

The consecutive gaps form a natural basis for all gaps.
-/

/-- Any gap is at least the largest consecutive gap involved. -/
theorem gap_lower_bound (n i j : ℕ) (hij : i < j) :
    generalGap n i j ≥ consecutiveGap n i := by
  sorry

/-!
# Part 8: Connection to Problem 144

Related to divisor sums and Egyptian fractions.
-/

/--
**Problem 144 Connection**

Problem #144 asks about representations of rationals as unit fractions
with denominators being divisors of n.

Both problems study the arithmetic of divisor sets.
-/

/-- The harmonic sum over divisors. -/
noncomputable def divisorHarmonicSum (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (1 : ℝ) / d

/-- σ_{-1}(n) = Σ_{d|n} 1/d. -/
axiom divisorHarmonicSum_formula (n : ℕ) (hn : n > 0) :
    divisorHarmonicSum n = (∑ d ∈ n.divisors, (1 : ℝ) / d)

/-!
# Part 9: Multiplicative Structure

How the conjecture behaves under multiplication.
-/

/--
**Multiplicative Considerations**

If gcd(m, n) = 1, then τ(mn) = τ(m) · τ(n).

The divisors of mn are products of divisors of m and n.

This affects the gap structure significantly.
-/
theorem numDivisors_mul_coprime (m n : ℕ) (hm : m > 0) (hn : n > 0) (hcop : Nat.Coprime m n) :
    numDivisors (m * n) = numDivisors m * numDivisors n := by
  sorry

/--
**Highly Composite Numbers**

Numbers with many divisors (like factorials, primorials) are
interesting test cases for the conjecture.
-/
def factorial_divisors (n : ℕ) : ℕ := numDivisors n.factorial

/-!
# Part 10: Problem Status

Summary and status.
-/

/-- The problem is open. -/
def erdos_884_status : String := "OPEN"

/-- Main formal statement. -/
theorem erdos_884_statement : ErdosConjecture884 ↔
    ∃ C : ℝ, C > 0 ∧ ∀ n > 1, allPairsSum n ≤ C * (1 + consecutivePairsSum n) := by
  rfl

/-!
# Summary

**Problem:** Is Σ_{i<j} 1/(d_j - d_i) ≪ 1 + Σ_i 1/(d_{i+1} - d_i)?

**Status:** OPEN

**Key Structure:**
- Left side: sum over ALL pairs of divisors
- Right side: sum over CONSECUTIVE pairs only
- Question: is the "all" sum bounded by the "consecutive" sum?

**Intuition:**
- Each gap d_j - d_i is a sum of consecutive gaps
- Consecutive gaps form a natural basis
- The conjecture says "all pairs" doesn't grow much faster than "consecutive pairs"

**Related:** Problem #144 (divisors and Egyptian fractions)
-/

end Erdos884
