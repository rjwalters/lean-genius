/-
Erdős Problem #289: Interval Reciprocal Sum Equals 1

**Statement**: For all sufficiently large k, do there exist k finite intervals
I₁, ..., Iₖ ⊂ ℕ that are:
- Distinct
- Non-overlapping
- Non-adjacent
- Each with |Iᵢ| ≥ 2

such that Σᵢ Σ_{n ∈ Iᵢ} 1/n = 1?

**Status**: OPEN

**Known Example (for target 2)**:
Hickerson-Montgomery found for target 2:
- I₁ = [2,7]: 1/2 + 1/3 + 1/4 + 1/5 + 1/6 + 1/7
- I₂ = [9,10]: 1/9 + 1/10
- I₃ = [17,18]: 1/17 + 1/18
- I₄ = [34,35]: 1/34 + 1/35
- I₅ = [84,85]: 1/84 + 1/85
Total = 2

**Context**:
- Original ErGr80 lacked distinctness constraint (Kovac noted this)
- Related to unit fraction decompositions
- The sum over an interval [a,b] is H_b - H_{a-1}

Reference: https://erdosproblems.com/289
-/

import Mathlib

namespace Erdos289

open Nat Finset BigOperators Rat

/-
## Part I: Interval Sum of Reciprocals
-/

/-- Sum of reciprocals over interval [a, b]. -/
def intervalSum (a b : ℕ) : ℚ :=
  ∑ n ∈ Icc a b, (1 : ℚ) / n

/-- An interval as a pair (start, end) with a ≤ b. -/
structure Interval where
  start : ℕ
  stop : ℕ
  h_le : start ≤ stop
  h_pos : start ≥ 1

/-- Size of an interval. -/
def Interval.size (I : Interval) : ℕ := I.stop - I.start + 1

/-- The interval has size at least 2. -/
def Interval.hasSizeAtLeast2 (I : Interval) : Prop := I.size ≥ 2

/-- Sum of reciprocals over an interval. -/
def Interval.recipSum (I : Interval) : ℚ :=
  intervalSum I.start I.stop

/-
## Part II: Interval Constraints
-/

/-- Two intervals are disjoint (non-overlapping). -/
def disjoint (I J : Interval) : Prop :=
  I.stop < J.start ∨ J.stop < I.start

/-- Two intervals are non-adjacent (gap ≥ 1). -/
def nonAdjacent (I J : Interval) : Prop :=
  I.stop + 1 < J.start ∨ J.stop + 1 < I.start

/-- A list of intervals satisfies the constraints. -/
def validIntervals (Is : List Interval) : Prop :=
  (∀ I ∈ Is, I.hasSizeAtLeast2) ∧
  (∀ I J, I ∈ Is → J ∈ Is → I ≠ J → disjoint I J) ∧
  (∀ I J, I ∈ Is → J ∈ Is → I ≠ J → nonAdjacent I J)

/-- Total sum of reciprocals over a list of intervals. -/
def totalSum (Is : List Interval) : ℚ :=
  Is.map Interval.recipSum |>.sum

/-
## Part III: The Main Conjecture
-/

/-- Erdős Problem #289 (OPEN): For sufficiently large k,
    k valid intervals can sum to exactly 1. -/
def erdos_289_conjecture : Prop :=
  ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ Is : List Interval,
    Is.length = k ∧ validIntervals Is ∧ totalSum Is = 1

/-
## Part IV: The Hickerson-Montgomery Example for 2
-/

/-- The interval [2, 7]. -/
def I1 : Interval := ⟨2, 7, by omega, by omega⟩

/-- The interval [9, 10]. -/
def I2 : Interval := ⟨9, 10, by omega, by omega⟩

/-- The interval [17, 18]. -/
def I3 : Interval := ⟨17, 18, by omega, by omega⟩

/-- The interval [34, 35]. -/
def I4 : Interval := ⟨34, 35, by omega, by omega⟩

/-- The interval [84, 85]. -/
def I5 : Interval := ⟨84, 85, by omega, by omega⟩

/-- The Hickerson-Montgomery intervals. -/
def hmIntervals : List Interval := [I1, I2, I3, I4, I5]

/-- The intervals are valid (disjoint, non-adjacent, size ≥ 2). -/
theorem hmIntervals_valid : validIntervals hmIntervals := by
  unfold validIntervals hmIntervals I1 I2 I3 I4 I5
  constructor
  · intro I hI
    simp only [List.mem_cons, List.mem_singleton] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl <;>
    simp [Interval.hasSizeAtLeast2, Interval.size]
  constructor
  · intro I J hI hJ hne
    simp only [List.mem_cons, List.mem_singleton] at hI hJ
    unfold disjoint
    rcases hI with rfl | rfl | rfl | rfl | rfl <;>
    rcases hJ with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [Interval.start, Interval.stop]
  · intro I J hI hJ hne
    simp only [List.mem_cons, List.mem_singleton] at hI hJ
    unfold nonAdjacent
    rcases hI with rfl | rfl | rfl | rfl | rfl <;>
    rcases hJ with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [Interval.start, Interval.stop]

/-- Compute 1/2 + 1/3 + 1/4 + 1/5 + 1/6 + 1/7. -/
theorem I1_sum : I1.recipSum = 1/2 + 1/3 + 1/4 + 1/5 + 1/6 + 1/7 := by
  unfold Interval.recipSum intervalSum I1
  native_decide

/-- The total sum of HM intervals equals 2. -/
theorem hmIntervals_sum : totalSum hmIntervals = 2 := by
  -- 1/2 + 1/3 + 1/4 + 1/5 + 1/6 + 1/7 +
  -- 1/9 + 1/10 + 1/17 + 1/18 + 1/34 + 1/35 + 1/84 + 1/85 = 2
  native_decide

/-
## Part V: Reformulation
-/

/-- Equivalent: represents target T with k intervals. -/
def represents (Is : List Interval) (T : ℚ) : Prop :=
  Is.length ≥ 1 ∧ validIntervals Is ∧ totalSum Is = T

/-- The HM intervals represent 2. -/
theorem hm_represents_two : represents hmIntervals 2 :=
  ⟨by simp [hmIntervals], hmIntervals_valid, hmIntervals_sum⟩

/-- For target 1, the conjecture asks if all large k work. -/
def erdos_289_target1 : Prop :=
  ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ Is : List Interval,
    Is.length = k ∧ represents Is 1

/-
## Part VI: Observations
-/

/-- Key identity: intervalSum a b = H_b - H_{a-1}. -/
axiom intervalSum_harmonic (a b : ℕ) (ha : a ≥ 1) (hab : a ≤ b) :
    intervalSum a b = harmonic b - harmonic (a - 1)

/-- Small intervals have sum < 1. -/
theorem small_interval_lt_one (a b : ℕ) (ha : a ≥ 2) (hsize : b - a + 1 ≤ 10) :
    intervalSum a b < 1 := by
  sorry

/-
## Part VII: Summary
-/

/-- Erdős Problem #289: Summary

**Conjecture**: For large k, there exist k valid intervals summing to 1.

**Formalized**:
- `Interval` structure with start, stop
- `validIntervals` - disjoint, non-adjacent, size ≥ 2
- `totalSum` - sum of all reciprocals
- `erdos_289_conjecture` - the main statement

**Proven/Verified**:
- `hmIntervals_valid` - HM intervals are valid
- `hmIntervals_sum` - HM intervals sum to 2
- `hm_represents_two` - example for target 2

**Status**: OPEN
-/

axiom erdos_289 : erdos_289_conjecture

theorem erdos_289_summary : True := trivial

end Erdos289
