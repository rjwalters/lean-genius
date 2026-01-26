/-
Erdős Problem #423: Sums of Consecutive Terms Sequence

Source: https://erdosproblems.com/423
Status: OPEN

Statement:
Let a₁ = 1, a₂ = 2. For k ≥ 3, define aₖ as the least integer > a_{k-1}
which is the sum of at least two consecutive terms of the sequence.

The sequence begins: 1, 2, 3, 5, 6, 8, 10, 11, ...

What is the asymptotic behaviour of this sequence?

Known:
- The sequence a(n) - n is nondecreasing and unbounded (Bolan, Tang 2024-2025)
- Infinitely many integers do not appear in the sequence

OEIS: A005243
References: [Er77c, p.71], [ErGr80, p.83]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Range
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Nat Finset

namespace Erdos423

/-! ## Part I: The Sequence Definition -/

/-- The Erdős-Hofstadter sequence: a₁ = 1, a₂ = 2, and for k ≥ 3,
    aₖ is the least integer > a_{k-1} that equals the sum of at least
    two consecutive terms a_i + a_{i+1} + ... + a_j for some i ≤ j < k. -/
noncomputable def consSeq : ℕ → ℕ := sorry -- Well-defined by greedy construction

/-- Initial values. -/
axiom consSeq_zero : consSeq 0 = 1
axiom consSeq_one : consSeq 1 = 2

/-- The sequence is strictly increasing. -/
axiom consSeq_strictMono : StrictMono consSeq

/-! ## Part II: Consecutive Sum Property -/

/-- The sum of consecutive terms a_i + a_{i+1} + ... + a_j. -/
noncomputable def consecutiveSum (i j : ℕ) : ℕ :=
  (Finset.Icc i j).sum consSeq

/-- A number m is a consecutive sum of the sequence up to index n
    if m = a_i + a_{i+1} + ... + a_j for some i ≤ j < n with j - i ≥ 1. -/
def IsConsecutiveSum (m n : ℕ) : Prop :=
  ∃ i j, i ≤ j ∧ j < n ∧ j > i ∧ consecutiveSum i j = m

/-- The defining property: a(k) is the least integer > a(k-1)
    that is a consecutive sum. -/
axiom consSeq_is_consecutive_sum (k : ℕ) (hk : k ≥ 2) :
    IsConsecutiveSum (consSeq k) k

/-- No smaller integer > a(k-1) is a consecutive sum. -/
axiom consSeq_minimal (k : ℕ) (hk : k ≥ 2) (m : ℕ)
    (hm₁ : consSeq (k - 1) < m) (hm₂ : m < consSeq k) :
    ¬IsConsecutiveSum m k

/-! ## Part III: Known Initial Values -/

/-- The first several terms of the sequence (OEIS A005243). -/
axiom consSeq_values :
    consSeq 2 = 3 ∧ consSeq 3 = 5 ∧ consSeq 4 = 6 ∧
    consSeq 5 = 8 ∧ consSeq 6 = 10 ∧ consSeq 7 = 11

/-- Verification: 3 = 1 + 2 (consecutive sum a₁ + a₂). -/
axiom verify_three : consecutiveSum 0 1 = 3

/-- Verification: 5 = 2 + 3 (consecutive sum a₂ + a₃). -/
axiom verify_five : consecutiveSum 1 2 = 5

/-! ## Part IV: Growth Properties -/

/-- The sequence grows at least linearly: a(n) ≥ n + 1. -/
axiom consSeq_lower_bound (n : ℕ) : consSeq n ≥ n + 1

/-- The excess a(n) - n is nondecreasing (Bolan, Tang). -/
axiom excess_nondecreasing :
    ∀ m n : ℕ, m ≤ n → consSeq m - m ≤ consSeq n - n

/-- The excess a(n) - n is unbounded (Bolan, Tang). -/
axiom excess_unbounded :
    Filter.Tendsto (fun n => (consSeq n : ℤ) - (n : ℤ)) Filter.atTop Filter.atTop

/-! ## Part V: Missing Numbers -/

/-- The set of positive integers that appear in the sequence. -/
def seqRange : Set ℕ := {m | ∃ n, consSeq n = m}

/-- The set of positive integers NOT in the sequence. -/
def missingNumbers : Set ℕ := {m | m ≥ 1 ∧ m ∉ seqRange}

/-- Infinitely many integers do not appear (Bolan, Tang). -/
axiom infinitely_many_missing : Set.Infinite missingNumbers

/-- 4 is the first missing number (not a consecutive sum at the right moment). -/
axiom four_is_missing : 4 ∈ missingNumbers

/-! ## Part VI: The Main Question -/

/--
**Erdős Problem #423 (OPEN):**
What is the asymptotic behaviour of the sequence?

Possible formulations:
1. Is a(n) ~ cn for some constant c > 1?
2. Does a(n)/n converge?
3. What is the density of seqRange?
-/
def ErdosQuestion423_convergence : Prop :=
  ∃ C : ℝ, C > 1 ∧
    Filter.Tendsto (fun n => (consSeq n : ℝ) / (n : ℝ)) Filter.atTop (nhds C)

def ErdosQuestion423_density : Prop :=
  ∃ d : ℝ, 0 < d ∧ d < 1 ∧
    Filter.Tendsto
      (fun N => ((Finset.range (N + 1)).filter (· ∈ seqRange)).card / (N + 1 : ℝ))
      Filter.atTop (nhds d)

/-! ## Part VII: Summary -/

/--
**Erdős Problem #423: Summary**

PROBLEM: Let a₁=1, a₂=2, and for k≥3, aₖ is the least integer > a_{k-1}
that is a sum of at least two consecutive terms. What is the asymptotic
behaviour?

STATUS: OPEN

KNOWN:
- Sequence: 1, 2, 3, 5, 6, 8, 10, 11, ... (OEIS A005243)
- a(n) - n is nondecreasing and unbounded (Bolan, Tang)
- Infinitely many integers are not in the sequence
- 4 is the first missing number
-/
theorem erdos_423_known :
    (∀ m n, m ≤ n → consSeq m - m ≤ consSeq n - n) ∧
    Set.Infinite missingNumbers := by
  exact ⟨excess_nondecreasing, infinitely_many_missing⟩

/-- The problem remains OPEN. -/
theorem erdos_423_status : True := trivial

end Erdos423
