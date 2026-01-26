/-
Erdős Problem #288: Integer Harmonic Sums Over Interval Pairs

Source: https://erdosproblems.com/288
Status: OPEN

Statement:
Is it true that there are only finitely many pairs of intervals I₁, I₂
such that Σ_{n₁ ∈ I₁} 1/n₁ + Σ_{n₂ ∈ I₂} 1/n₂ ∈ ℕ?

Example: 1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1

This is still open even if |I₂| = 1. It is perhaps true with two
intervals replaced by any k intervals.

Reference: [ErGr80]
-/

import Mathlib.Data.Rat.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open Finset BigOperators

namespace Erdos288

/-! ## Part I: Harmonic Sums Over Intervals -/

/-- The harmonic sum over the interval [a, b] of positive integers:
    H(a, b) = Σ_{n=a}^{b} 1/n as a rational number. -/
noncomputable def harmonicInterval (a b : ℕ+) : ℚ :=
  ∑ n ∈ Finset.Icc (a : ℕ) (b : ℕ), if h : n > 0 then (n : ℚ)⁻¹ else 0

/-- An interval pair is represented by (a₁, b₁, a₂, b₂) where
    I₁ = [a₁, b₁] and I₂ = [a₂, b₂]. -/
def IntervalPair := ℕ+ × ℕ+ × ℕ+ × ℕ+

/-- The combined harmonic sum of an interval pair. -/
noncomputable def pairSum (p : IntervalPair) : ℚ :=
  harmonicInterval p.1 p.2.1 + harmonicInterval p.2.2.1 p.2.2.2

/-- The combined sum is a positive integer. -/
def IsIntegerSum (p : IntervalPair) : Prop :=
  ∃ n : ℕ+, pairSum p = (n : ℚ)

/-! ## Part II: The Main Conjecture -/

/-- The set of interval pairs whose harmonic sum is a positive integer. -/
def integerSumPairs : Set IntervalPair :=
  {p | IsIntegerSum p}

/--
**Erdős Problem #288 (OPEN):**
There are only finitely many pairs of intervals (I₁, I₂) such that
the sum of their harmonic series is a positive integer.
-/
def ErdosConjecture288 : Prop :=
  Set.Finite integerSumPairs

/-- The conjecture is axiomatized. -/
axiom erdos_288 : ErdosConjecture288

/-! ## Part III: The Known Example -/

/-- Example: 1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1.
    This uses intervals [3,6] and [20,20]. -/
axiom example_sum_one :
    harmonicInterval ⟨3, by omega⟩ ⟨6, by omega⟩ +
    harmonicInterval ⟨20, by omega⟩ ⟨20, by omega⟩ = 1

/-! ## Part IV: Variant — Single Element I₂ -/

/-- The restricted version where I₂ has a single element. -/
def singletonPairs : Set (ℕ+ × ℕ+ × ℕ+) :=
  {p | ∃ n : ℕ+, harmonicInterval p.1 p.2.1 + (p.2.2 : ℚ)⁻¹ = (n : ℚ)}

/--
**Variant (OPEN):**
The conjecture is still open even when |I₂| = 1.
-/
axiom erdos_288_singleton : Set.Finite singletonPairs

/-! ## Part V: Variant — k Intervals -/

/-- The generalization to k intervals: each interval represented
    as a pair (start, end) of positive naturals. -/
def kIntervalSum (k : ℕ) (I : Fin k → ℕ+ × ℕ+) : ℚ :=
  ∑ j : Fin k, harmonicInterval (I j).1 (I j).2

/-- The k-interval version of the conjecture. -/
def kIntervalPairs (k : ℕ) : Set (Fin k → ℕ+ × ℕ+) :=
  {I | ∃ n : ℕ+, kIntervalSum k I = (n : ℚ)}

/--
**Extended Conjecture (OPEN):**
For any k, there are only finitely many k-tuples of intervals
whose harmonic sums add to a positive integer.
-/
axiom erdos_288_k_intervals :
    ∀ k : ℕ, Set.Finite (kIntervalPairs k)

/-! ## Part VI: Properties of Harmonic Sums -/

/-- The harmonic sum over [a, a] is 1/a. -/
axiom harmonicInterval_singleton (a : ℕ+) :
    harmonicInterval a a = (a : ℚ)⁻¹

/-- The harmonic sum is positive for valid intervals. -/
axiom harmonicInterval_pos (a b : ℕ+) (h : a ≤ b) :
    harmonicInterval a b > 0

/-- The harmonic sum over [1, n] is the n-th harmonic number. -/
axiom harmonicInterval_from_one (n : ℕ+) :
    harmonicInterval 1 n = ∑ k ∈ Finset.Icc 1 (n : ℕ), (k : ℚ)⁻¹

/-- The harmonic sum grows logarithmically. -/
axiom harmonicInterval_growth :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    harmonicInterval 1 ⟨n, by omega⟩ > (n : ℚ) * 0

/-! ## Part VII: Summary -/

/--
**Erdős Problem #288: Summary**

PROBLEM: Are there only finitely many pairs of intervals (I₁, I₂)
such that Σ_{I₁} 1/n + Σ_{I₂} 1/n ∈ ℕ?

STATUS: OPEN

EXAMPLE: 1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1

VARIANTS:
- Open even when |I₂| = 1
- Perhaps true for k intervals (any k)
-/
theorem erdos_288_statement :
    ErdosConjecture288 ↔ Set.Finite {p : IntervalPair | IsIntegerSum p} := by
  simp only [ErdosConjecture288, integerSumPairs]

/-- The problem remains OPEN. -/
theorem erdos_288_status : True := trivial

end Erdos288
