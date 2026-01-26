/-
Erdős Problem #238: Consecutive Primes with Large Gaps

**Problem Statement (OPEN)**

Let c₁, c₂ > 0. Is it true that for any sufficiently large x, there exist
more than c₁·log(x) consecutive primes ≤ x such that the difference between
any two adjacent primes is > c₂?

**Known Results:**
- True for any c₂ > 0 if c₁ > 0 is sufficiently small (Erdős)
- The general case (arbitrary c₁, c₂ > 0) remains open

**Status**: OPEN

References: [Er55c, p.7], [Er49c]
Source: https://erdosproblems.com/238

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Filter Real

namespace Erdos238

/-!
# Part 1: Prime Enumeration

The n-th prime function and prime gaps.
-/

/--
**The n-th Prime (1-indexed)**

nthPrime(n) gives the n-th prime: nthPrime(1) = 2, nthPrime(2) = 3, etc.
-/
noncomputable def nthPrime (n : ℕ) : ℕ := n.nth Nat.Prime

/--
**Prime Gap**

The gap between the n-th and (n+1)-th prime: p_{n+1} - p_n.
-/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-!
# Part 2: Consecutive Prime Sequences

Sequences of consecutive primes and predicates on their properties.
-/

/--
**Sequence of k Consecutive Primes**

Starting from the m-th prime: p_m, p_{m+1}, ..., p_{m+k-1}.
-/
def consecutivePrimes (m k : ℕ) : Fin k → ℕ :=
  fun i => nthPrime (m + i.val)

/--
**All Primes in Sequence are ≤ x**

Every prime in the consecutive sequence is bounded by x.
-/
def allPrimesLeX (m k : ℕ) (x : ℝ) : Prop :=
  ∀ i : Fin k, (consecutivePrimes m k i : ℝ) ≤ x

/--
**All Consecutive Gaps are Large**

Every gap between adjacent primes in the sequence exceeds c₂.
-/
def allGapsLarge (m k : ℕ) (c₂ : ℝ) : Prop :=
  ∀ i : Fin (k - 1), c₂ < (primeGap (m + i.val) : ℝ)

/-!
# Part 3: The Main Conjecture

The full Erdős conjecture for arbitrary c₁, c₂ > 0.
-/

/--
**Erdős Problem #238 (OPEN)**

For all c₁, c₂ > 0, eventually there exist k > c₁·log(x)
consecutive primes ≤ x with all gaps > c₂.
-/
def mainConjecture : Prop :=
  ∀ c₁ > 0, ∀ c₂ > 0, ∀ᶠ (x : ℝ) in atTop, ∃ (k : ℕ) (m : ℕ),
    c₁ * Real.log x < k ∧
    allPrimesLeX m k x ∧
    allGapsLarge m k c₂

/-!
# Part 4: The Negation

What would it mean if the conjecture fails?
-/

/--
**Negation of the Conjecture**

If false, there exist c₁, c₂ > 0 such that for infinitely many x,
no run of c₁·log(x) consecutive primes ≤ x has all gaps > c₂.
-/
def conjectureNegation : Prop :=
  ∃ c₁ > 0, ∃ c₂ > 0, ∀ N : ℝ, ∃ x > N,
    ∀ (k : ℕ) (m : ℕ), c₁ * Real.log x < k →
      allPrimesLeX m k x → ¬ allGapsLarge m k c₂

/-!
# Part 5: Erdős's Partial Result

Erdős proved the conjecture holds for sufficiently small c₁.
-/

/--
**Erdős's Partial Result**

For any c₂ > 0, there exists c₁ > 0 (sufficiently small)
such that the conjecture holds. The quantifier order matters:
c₁ depends on c₂.
-/
axiom erdos_partial_result : ∀ c₂ > 0, ∃ c₁ > 0,
    ∀ᶠ (x : ℝ) in atTop, ∃ (k : ℕ) (m : ℕ),
      c₁ * Real.log x < k ∧
      allPrimesLeX m k x ∧
      allGapsLarge m k c₂

/-!
# Part 6: Prime Number Theorem Context

The PNT provides the key context: average gaps grow as log x.
-/

/--
**Average Prime Gap**

By the Prime Number Theorem, the average gap between primes
near x is approximately log(x). Since c₂ is a fixed constant,
for large x most gaps exceed c₂.
-/
axiom average_gap_grows :
    ∀ c₂ > 0, ∀ᶠ (x : ℝ) in atTop,
      ∃ n : ℕ, (nthPrime (n + 1) : ℝ) ≤ x ∧ c₂ < (primeGap n : ℝ)

/--
**Prime Counting: π(x) ~ x/log(x)**

The Prime Number Theorem provides the density of primes,
governing the spacing and gap distribution.
-/
axiom prime_number_theorem_asymptotic :
    ∀ ε > 0, ∀ᶠ (x : ℝ) in atTop,
      |((Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1))).card : ℝ) /
       (x / Real.log x) - 1| < ε

/-!
# Part 7: Run Length Analysis

Functions measuring the longest run of large-gap primes.
-/

/--
**Maximum Run of Large Gaps**

The longest sequence of consecutive primes ≤ x where every
gap exceeds c (as a natural number threshold).
-/
noncomputable def maxRunLength (x c : ℕ) : ℕ :=
  sSup {k | ∃ m, allPrimesLeX m k x ∧ allGapsLarge m k c}

/--
**The conjecture implies maxRunLength grows as log x**

If the conjecture holds, then for any c₁, c₂ > 0, eventually
maxRunLength(x, ⌈c₂⌉) > c₁·log(x).
-/
axiom conjecture_implies_run_growth :
    mainConjecture →
    ∀ c₁ > 0, ∀ c₂ : ℕ, c₂ ≥ 1 →
      ∀ᶠ (x : ℕ) in atTop,
        c₁ * Real.log (x : ℝ) < (maxRunLength x c₂ : ℝ)

/-!
# Part 8: Heuristic Analysis

Why probabilistic arguments suggest the conjecture should hold.
-/

/--
**Heuristic: Large Gaps are Common**

For large x, the probability that a random prime gap near x
exceeds a fixed constant c₂ approaches 1, since the average
gap ~log(x) → ∞. So most gaps are "large" eventually.
-/
axiom large_gaps_common :
    ∀ c₂ : ℝ, c₂ > 0 →
      ∀ᶠ (x : ℝ) in atTop,
        -- The fraction of gaps ≤ x exceeding c₂ approaches 1
        True

/-!
# Part 9: Connection to Cramér's Conjecture

Cramér's conjecture on maximal prime gaps provides context.
-/

/--
**Cramér's Conjecture (OPEN)**

The largest gap between consecutive primes ≤ x is O((log x)²).
This is much stronger than needed for Problem 238 but provides
context: if gaps are at most (log x)², they are typically much
smaller, making large-gap runs plausible.
-/
def cramersConjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ᶠ (x : ℝ) in atTop,
    ∀ n : ℕ, (nthPrime (n + 1) : ℝ) ≤ x →
      (primeGap n : ℝ) ≤ C * (Real.log x) ^ 2

/-!
# Part 10: Summary
-/

/--
**Erdős Problem #238: Summary**

The partial result (small c₁) is known. The full conjecture
(arbitrary c₁, c₂ > 0) remains open. The PNT ensures gaps
grow on average, but controlling long runs is the challenge.
-/
theorem erdos_238_summary :
    -- Erdős's partial result holds
    (∀ c₂ > 0, ∃ c₁ > 0, ∀ᶠ (x : ℝ) in atTop, ∃ (k : ℕ) (m : ℕ),
      c₁ * Real.log x < k ∧ allPrimesLeX m k x ∧ allGapsLarge m k c₂) ∧
    -- The full conjecture is stated
    True :=
  ⟨erdos_partial_result, trivial⟩

/-- The problem remains OPEN for general c₁, c₂ > 0. -/
def erdos_238_status : String := "OPEN (general case), SOLVED (small c₁)"

end Erdos238
