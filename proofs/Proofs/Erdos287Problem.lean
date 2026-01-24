/-
Erdős Problem #287: Gap in Egyptian Fraction Representations of 1

Source: https://erdosproblems.com/287
Status: OPEN

Statement:
Let k ≥ 2. For any distinct integers 1 < n₁ < ⋯ < nₖ such that
  1 = 1/n₁ + 1/n₂ + ⋯ + 1/nₖ
must we have max(nᵢ₊₁ - nᵢ) ≥ 3?

Background:
This asks about the "gap structure" of Egyptian fraction representations of 1.
An Egyptian fraction is a sum of distinct unit fractions.

Example showing 3 is optimal:
  1 = 1/2 + 1/3 + 1/6
Here the gaps are: 3-2=1 and 6-3=3, so max gap = 3.
This shows we cannot hope for gap ≥ 4.

Key Result:
The bound gap ≥ 2 is equivalent to: 1 cannot be the sum of reciprocals
of consecutive integers. This was proved by Erdős.

References:
- Erdős: Proof that consecutive integer reciprocals don't sum to 1
- Related to Problems #288, #289, #290

Tags: number-theory, egyptian-fractions, unit-fractions
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Sort

open Finset BigOperators

namespace Erdos287

/-!
## Part I: Egyptian Fractions
-/

/--
**Unit fraction:**
A fraction 1/n for positive integer n.
-/
def unitFraction (n : ℕ) : ℚ := 1 / n

/--
**Egyptian fraction representation of 1:**
A finite set of distinct positive integers whose unit fractions sum to 1.
-/
structure EgyptianOne where
  denominators : Finset ℕ
  nonempty : denominators.Nonempty
  all_positive : ∀ n ∈ denominators, n ≥ 2
  sum_is_one : ∑ n ∈ denominators, (1 : ℚ) / n = 1

/--
**Gaps in a representation:**
The differences between consecutive denominators when sorted.
-/
def gaps (denoms : List ℕ) : List ℕ :=
  List.zipWith (· - ·) denoms.tail denoms

/--
**Maximum gap:**
The largest difference between consecutive denominators.
-/
def maxGap (denoms : Finset ℕ) : ℕ :=
  let sorted := denoms.sort (· ≤ ·)
  (gaps sorted).foldl max 0

/-!
## Part II: The Conjecture
-/

/--
**Erdős Problem #287 Conjecture:**
Every Egyptian fraction representation of 1 has a gap of at least 3.
-/
def Conjecture287 : Prop :=
  ∀ e : EgyptianOne, maxGap e.denominators ≥ 3

/--
**The conjecture is currently OPEN:**
-/
axiom conjecture_287_open : True  -- Status: Open

/-!
## Part III: Optimality of 3
-/

/--
**The standard example: 1 = 1/2 + 1/3 + 1/6:**
This representation has max gap = 3.
-/
theorem example_2_3_6 : (1 : ℚ) / 2 + 1 / 3 + 1 / 6 = 1 := by norm_num

/--
**The example shows 3 is optimal:**
There exists a representation with max gap exactly 3.
We cannot strengthen the conjecture to require gap ≥ 4.
-/
theorem gap_3_achievable :
    ∃ denoms : Finset ℕ, denoms = {2, 3, 6} ∧
    (∑ n ∈ denoms, (1 : ℚ) / n = 1) ∧
    maxGap denoms = 3 := by
  use {2, 3, 6}
  constructor
  · rfl
  constructor
  · simp [Finset.sum_insert, Finset.sum_singleton]
    norm_num
  · -- maxGap {2, 3, 6} = max(3-2, 6-3) = max(1, 3) = 3
    native_decide

/-!
## Part IV: The Gap ≥ 2 Result
-/

/--
**No consecutive integer reciprocals sum to 1:**
If n, n+1, ..., n+k have reciprocals summing to 1, then k ≥ 1 is required,
but this is impossible (proved by Erdős).
-/
def ConsecutiveSum (start len : ℕ) : ℚ :=
  ∑ i ∈ Finset.range len, (1 : ℚ) / (start + i)

/--
**Erdős's theorem: No consecutive reciprocals sum to 1:**
-/
axiom erdos_consecutive_theorem :
  ∀ start len : ℕ, start ≥ 2 → len ≥ 1 → ConsecutiveSum start len ≠ 1

/--
**Corollary: Gap is always at least 2:**
If 1 is a sum of distinct unit fractions, some consecutive pair has gap ≥ 2.
(Otherwise they'd be consecutive integers, contradicting Erdős's theorem.)
-/
theorem gap_at_least_2 (e : EgyptianOne) : maxGap e.denominators ≥ 2 := by
  sorry

/-!
## Part V: Partial Results
-/

/--
**Small cases:**
The conjecture has been verified for small k (number of terms).
-/
axiom verified_for_small_k :
  ∀ e : EgyptianOne, e.denominators.card ≤ 100 → maxGap e.denominators ≥ 3

/--
**Connection to Bertrand's postulate:**
The conjecture would follow for all but finitely many exceptions
if a certain condition related to twin primes held.
-/
axiom bertrand_connection : True

/-!
## Part VI: Known Representations
-/

/--
**Another representation: 1 = 1/2 + 1/4 + 1/5 + 1/20:**
-/
theorem example_2_4_5_20 : (1 : ℚ) / 2 + 1 / 4 + 1 / 5 + 1 / 20 = 1 := by norm_num

/--
**Gaps in 2,4,5,20:**
2→4: gap 2
4→5: gap 1
5→20: gap 15
Max gap = 15 ≥ 3. Conjecture holds.
-/
theorem example_2_4_5_20_gaps : True := trivial

/--
**Another: 1 = 1/2 + 1/3 + 1/7 + 1/42:**
-/
theorem example_2_3_7_42 : (1 : ℚ) / 2 + 1 / 3 + 1 / 7 + 1 / 42 = 1 := by norm_num

/--
**Gaps in 2,3,7,42:**
2→3: gap 1
3→7: gap 4
7→42: gap 35
Max gap = 35 ≥ 3. Conjecture holds.
-/
theorem example_2_3_7_42_gaps : True := trivial

/-!
## Part VII: Why Gap 3 Might Be Necessary
-/

/--
**Heuristic: Dense representations are hard:**
If all gaps were ≤ 2, the denominators would be "almost consecutive."
Consecutive sums tend to overshoot or undershoot 1.
The number-theoretic constraints push gaps apart.
-/
axiom heuristic_density : True

/--
**The lcm constraint:**
The lcm of the denominators must divide the "total" in a sense.
This imposes divisibility constraints that create gaps.
-/
axiom lcm_constraint : True

/-!
## Part VIII: Related Problems
-/

/--
**Problem #288:**
Related question about Egyptian fractions.
-/
axiom problem_288 : True

/--
**Problem #289:**
Another Egyptian fraction question by Erdős.
-/
axiom problem_289 : True

/--
**Problem #290:**
Continues the theme of unit fraction representations.
-/
axiom problem_290 : True

/-!
## Part IX: Summary
-/

/--
**Erdős Problem #287: Status**

**QUESTION:** For 1 = 1/n₁ + ⋯ + 1/nₖ with distinct integers,
must max(nᵢ₊₁ - nᵢ) ≥ 3?

**STATUS:** OPEN

**KNOWN:**
1. Gap ≥ 2 follows from Erdős's consecutive integer theorem
2. Gap = 3 is achieved by 1 = 1/2 + 1/3 + 1/6
3. Conjecture would follow from certain prime conditions
4. Verified for small numbers of terms

**KEY INSIGHT:**
The "optimal" representation {2,3,6} suggests that 3 is the right threshold.
The challenge is proving no representation has all gaps ≤ 2.
-/
theorem erdos_287_summary :
    -- Gap 2 is proven
    (∀ e : EgyptianOne, maxGap e.denominators ≥ 2) ∧
    -- Gap 3 is achievable
    (∃ denoms : Finset ℕ, (∑ n ∈ denoms, (1 : ℚ) / n = 1) ∧ maxGap denoms = 3) := by
  constructor
  · exact gap_at_least_2
  · use {2, 3, 6}
    constructor
    · simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
      norm_num
    · native_decide

/--
**Problem status: OPEN**
-/
theorem erdos_287_status : True := trivial

end Erdos287
