/-
Erdős Problem #693: Divisor Gaps in Intervals

Let k ≥ 2 and n be sufficiently large. Consider the set A of integers in [n, n^k]
that have a divisor in the interval (n, 2n). Order A as a₁ < a₂ < ···.

Problem: Is the maximum gap max_i(a_{i+1} - a_i) bounded by (log n)^O(1)?

In other words, are integers with "medium-sized" divisors densely distributed
with only polylogarithmic gaps?

This is Problem #693 from erdosproblems.com.
Related to Problem #446.

Reference: https://erdosproblems.com/693

Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# Erdős Problem 693: Divisor Gaps in Intervals

*Reference:* [erdosproblems.com/693](https://www.erdosproblems.com/693)
-/

open Nat Finset Set
open Filter

namespace Erdos693

/-- An integer m has a divisor in the interval (a, b) -/
def hasDivisorInInterval (m : ℕ) (a b : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ m ∧ a < d ∧ d < b

/-- The set A(n, k): integers in [n, n^k] with a divisor in (n, 2n) -/
def setA (n k : ℕ) : Set ℕ :=
  {m | n ≤ m ∧ m ≤ n^k ∧ hasDivisorInInterval m n (2*n)}

/-- setA is finite for n ≥ 1 -/
lemma setA_finite (n k : ℕ) (hn : n ≥ 1) : (setA n k).Finite := by
  apply Set.Finite.subset (Set.finite_Icc n (n^k))
  intro m hm
  exact ⟨hm.1, hm.2.1⟩

/-- Convert setA to a finset when finite -/
noncomputable def setAFinset (n k : ℕ) (hn : n ≥ 1) : Finset ℕ :=
  (setA_finite n k hn).toFinset

/-- The ordered list of elements in A -/
noncomputable def orderedA (n k : ℕ) (hn : n ≥ 1) : List ℕ :=
  (setAFinset n k hn).sort (· ≤ ·)

/-- Gap between consecutive elements in the ordered list -/
def consecutiveGaps (L : List ℕ) : List ℕ :=
  L.zipWith (fun a b => b - a) L.tail

/-- Maximum gap in the list -/
noncomputable def maxGap (L : List ℕ) : ℕ :=
  (consecutiveGaps L).foldl max 0

/-- The maximum gap for the set A(n, k) -/
noncomputable def maxGapA (n k : ℕ) (hn : n ≥ 1) : ℕ :=
  maxGap (orderedA n k hn)

/-!
## Main Problem

Erdős Problem #693: Is max_i(a_{i+1} - a_i) bounded by (log n)^O(1)?

This asks whether there exist constants C > 0 and α > 0 such that
for all sufficiently large n, the maximum gap is at most C·(log n)^α.
-/

/-- Polylogarithmic bound: there exist C, α such that maxGap ≤ C·(log n)^α -/
def polylogBoundedGap (k : ℕ) : Prop :=
  ∃ C α : ℝ, C > 0 ∧ α > 0 ∧
    ∀ᶠ n in atTop, ∀ hn : n ≥ 1,
      (maxGapA n k hn : ℝ) ≤ C * (Real.log n)^α

/-- Erdős Problem #693: Is the maximum gap polylogarithmically bounded? -/
@[category research open, AMS 11]
theorem erdos_693 (k : ℕ) (hk : k ≥ 2) :
    answer(sorry) ↔ polylogBoundedGap k := by
  sorry

/-!
## Properties of the Set A

### Basic Observations
-/

/-- Every element of A has at least one divisor in (n, 2n) by definition -/
lemma mem_setA_has_divisor {n k m : ℕ} (hm : m ∈ setA n k) :
    hasDivisorInInterval m n (2*n) :=
  hm.2.2

/-- If d is a divisor of m in (n, 2n), then m = d·q for some q -/
lemma divisor_factorization {m d : ℕ} (hd : d ∣ m) :
    ∃ q, m = d * q :=
  hd

/-- The range [n, n^k] has cardinality n^k - n + 1 -/
lemma range_card (n k : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    (Finset.Icc n (n^k)).card = n^k - n + 1 := by
  simp [Finset.card_Icc]
  omega

/-!
### Density Considerations

If A is dense (has many elements), gaps are small.
The question is about the exact growth rate of the maximum gap.
-/

/-- Trivial upper bound: maximum gap ≤ n^k - n (the entire range) -/
lemma maxGap_trivial_upper (n k : ℕ) (hn : n ≥ 1) :
    maxGapA n k hn ≤ n^k - n := by
  sorry

/-- Lower bound: there must be at least one gap of size ≥ (range size)/(card A) -/
-- Pigeonhole principle: if A has |A| elements in range of size R,
-- average gap is R/|A|, so max gap ≥ R/|A|
lemma maxGap_pigeonhole (n k : ℕ) (hn : n ≥ 1) (hA : (setA n k).Nonempty) :
    ∃ gap : ℕ, gap ≤ maxGapA n k hn ∧
      gap * (setAFinset n k hn).card ≥ n^k - n := by
  sorry

/-!
### Counting Elements of A

To understand gaps, we need to estimate |A|.
-/

/-- Count of elements with a divisor in (n, 2n) -/
noncomputable def countA (n k : ℕ) (hn : n ≥ 1) : ℕ :=
  (setAFinset n k hn).card

/-- Heuristic: m has a divisor in (n, 2n) iff some d in (n, 2n) divides m -/
-- The probability that a random d divides m is roughly 1/d
-- So the "probability" m has such a divisor is roughly ∑_{n<d<2n} 1/d ≈ log(2)
-- This suggests A should be dense, making gaps small

/-!
## Related Problems and Connections
-/

/-- Alternative formulation: uniform gap bound -/
def uniformGapBound (n k : ℕ) (hn : n ≥ 1) (B : ℕ) : Prop :=
  ∀ i : ℕ, i + 1 < (orderedA n k hn).length →
    (orderedA n k hn).get ⟨i+1, by omega⟩ -
    (orderedA n k hn).get ⟨i, by omega⟩ ≤ B

/-- The problem asks if B can be taken as C·(log n)^α for some constants -/
@[category research open, AMS 11]
theorem erdos_693_uniform (k : ℕ) (hk : k ≥ 2) :
    answer(sorry) ↔
    ∃ C α : ℝ, C > 0 ∧ α > 0 ∧
      ∀ᶠ n in atTop, ∀ hn : n ≥ 1,
        uniformGapBound n k hn ⌈C * (Real.log n)^α⌉₊ := by
  sorry

/-!
### Special Cases
-/

/-- For k = 2, the range is [n, n²] -/
-- This is the "quadratic" case: integers in [n, n²] with a divisor in (n, 2n)

/-- For very large k, the range [n, n^k] becomes huge -/
-- Gaps might be easier to control when the range is larger

/-!
## Connections to Divisor Distribution

The problem connects to classical questions about divisor distribution:
- How many integers up to x have a divisor in (y, 2y)?
- This is related to the Hooley divisor function and sieve methods
-/

/-- Classical: count of n ≤ x with a divisor in (y, 2y) is ~ x·log(2)/log(y) -/
-- This heuristic suggests A should have density ~ 1/log(n) in [n, n^k]
-- If true, |A| ~ (n^k - n)/log(n), so average gap ~ log(n)

axiom divisor_density_heuristic :
  ∀ᶠ n in atTop, ∀ k ≥ 2, ∀ hn : n ≥ 1,
    (countA n k hn : ℝ) ≥ (n^k - n : ℝ) / (2 * Real.log n)

/-!
## Problem Status
-/

/-- Summary: Erdős Problem #693 asks about polylogarithmic bounds on gaps
    between integers with medium-sized divisors. OPEN. -/
@[category research open, AMS 11]
theorem erdos_693_status :
    answer(sorry) ↔ polylogBoundedGap 2 := by
  sorry

end Erdos693

-- Placeholder for main result
theorem erdos_693_placeholder : True := trivial
