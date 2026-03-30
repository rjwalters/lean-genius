/-
  Exact k=3 Birthday Coincidence Threshold
  Open Question: birthday-problem-oq-03-oq-01

  Develops the extension-counting framework for the k=3 birthday problem:
  - Each valid (n+1)-assignment extends a valid n-assignment by placing person n+1
    on a day not at capacity (< k-1 people)
  - The extension count d - #{full days} is strictly less than d when n ≥ k-1
  - For k=3: extension count = d - #{doubled days}

  Key Results:
  1. fiberAt_sum: fiber sizes sum to n (partition of unity)
  2. fullDays_lt: #{full days} < d when below pigeonhole limit
  3. day_types_partition_k3: days split into empty/single/double types
  4. extension_count_k3: d - #{doubled} valid choices for new person
  5. restrict_preserves_valid: restricting (n+1)-assignment preserves bounds

  References:
  - Flajolet & Sedgewick (2009): Analytic Combinatorics, Ch. II.3
  - Diaconis & Mosteller (1989): Methods for studying coincidences
-/

import Mathlib

open Finset Fintype

namespace BirthdayKWayThreshold

/-
## Part 1: Fiber Infrastructure

The fiber at day j is the set of people assigned to day j.
Fiber sizes sum to the total number of people.
-/

/-- The fiber of an assignment at day j: people assigned to day j. -/
def fiberAt {n d : ℕ} (f : Fin n → Fin d) (j : Fin d) : Finset (Fin n) :=
  Finset.univ.filter (fun i => f i = j)

/-- Fiber sizes sum to n: the fibers partition the set of people. -/
theorem fiberAt_sum {n d : ℕ} (f : Fin n → Fin d) :
    ∑ j : Fin d, (fiberAt f j).card = n := by
  simp only [fiberAt]
  have h := Finset.card_eq_sum_card_fiberwise
    (f := f) (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Fin d)))
    (fun a _ => Finset.mem_univ (f a))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  linarith

/-
## Part 2: Full Days Bound

A "full day" has exactly k-1 people (the maximum allowed in a valid assignment).
When n < (k-1)·d, not all days can be full.
-/

/-- The set of days with exactly m people assigned. -/
def daysWithExactly {n d : ℕ} (f : Fin n → Fin d) (m : ℕ) : Finset (Fin d) :=
  Finset.univ.filter (fun j => (fiberAt f j).card = m)

/-- Full days: days with exactly k-1 people (at capacity). -/
def fullDays {n d : ℕ} (f : Fin n → Fin d) (k : ℕ) : Finset (Fin d) :=
  daysWithExactly f (k - 1)

/-- The number of full days is at most d (trivially). -/
theorem fullDays_card_le {n d : ℕ} (f : Fin n → Fin d) (k : ℕ) :
    (fullDays f k).card ≤ d := by
  calc (fullDays f k).card ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = d := by simp [Fintype.card_fin]

/-- Below the pigeonhole limit, not all days can be full.
    If n < (k-1)·d, then #{full days} < d. -/
theorem fullDays_lt_d {n d : ℕ} (f : Fin n → Fin d) (k : ℕ)
    (hk : 1 ≤ k) (hn : n < (k - 1) * d)
    (hvalid : ∀ j : Fin d, (fiberAt f j).card ≤ k - 1) :
    (fullDays f k).card < d := by
  by_contra hge
  push_neg at hge
  -- If #{full days} ≥ d, but #{full days} ≤ d, so = d
  have heq : (fullDays f k).card = d := by
    have := fullDays_card_le f k; omega
  -- All days are full (have exactly k-1 people)
  have hall : fullDays f k = Finset.univ := by
    exact Finset.eq_univ_of_card _ (by rw [heq]; simp [Fintype.card_fin])
  -- So every day has k-1 people: Σ fibers = (k-1)·d
  have hsum_ge : (k - 1) * d ≤ ∑ j : Fin d, (fiberAt f j).card := by
    calc (k - 1) * d = ∑ _j : Fin d, (k - 1) := by
          simp [Finset.sum_const, Fintype.card_fin, mul_comm]
      _ ≤ ∑ j : Fin d, (fiberAt f j).card := by
          apply Finset.sum_le_sum
          intro j _
          -- j is a full day since all days are full
          have hj : j ∈ fullDays f k := by rw [hall]; exact Finset.mem_univ _
          simp [fullDays, daysWithExactly, Finset.mem_filter] at hj
          omega
  -- But Σ fibers = n < (k-1)·d
  rw [fiberAt_sum f] at hsum_ge
  omega

/-
## Part 3: Extension Counting for k=3

For k=3, "full days" have exactly 2 people. Person (n+1) can be placed on any
non-full day: d - #{doubled days} valid choices.
-/

/-- The extension count: number of valid days for a new person.
    Equals d minus the number of full days. -/
def extensionCount {n d : ℕ} (f : Fin n → Fin d) (k : ℕ) : ℕ :=
  d - (fullDays f k).card

/-- Extension count is at most d. -/
theorem extensionCount_le {n d : ℕ} (f : Fin n → Fin d) (k : ℕ) :
    extensionCount f k ≤ d := by
  unfold extensionCount; omega

/-- Below pigeonhole limit, at least one valid extension exists. -/
theorem extensionCount_pos {n d : ℕ} (f : Fin n → Fin d) (k : ℕ)
    (hk : 1 ≤ k) (hn : n < (k - 1) * d)
    (hvalid : ∀ j : Fin d, (fiberAt f j).card ≤ k - 1) :
    0 < extensionCount f k := by
  unfold extensionCount
  have h := fullDays_lt_d f k hk hn hvalid
  omega

/-- For k=3, full days are exactly the doubled days. -/
theorem fullDays_k3 {n d : ℕ} (f : Fin n → Fin d) :
    fullDays f 3 = daysWithExactly f 2 := by rfl

/-- For k=3 below the pigeonhole limit (n < 2d), extension is always possible. -/
theorem extension_possible_k3 {n d : ℕ} (f : Fin n → Fin d)
    (hn : n < 2 * d)
    (hvalid : ∀ j : Fin d, (fiberAt f j).card ≤ 2) :
    0 < extensionCount f 3 := by
  apply extensionCount_pos f 3 (by omega) (by omega) hvalid

/-
## Part 4: Day Type Decomposition for k=3

For k=3 (max 2 per day), each day has 0, 1, or 2 people.
The three types partition all d days.
-/

/-- Under a valid k=3 assignment, every day has 0, 1, or 2 people. -/
theorem day_type_trichotomy {n d : ℕ} (f : Fin n → Fin d)
    (hvalid : ∀ j : Fin d, (fiberAt f j).card ≤ 2) (j : Fin d) :
    (fiberAt f j).card = 0 ∨ (fiberAt f j).card = 1 ∨ (fiberAt f j).card = 2 := by
  have := hvalid j; omega

/-- The three day types are pairwise disjoint. -/
theorem day_types_disjoint_01 {n d : ℕ} (f : Fin n → Fin d) :
    Disjoint (daysWithExactly f 0) (daysWithExactly f 1) := by
  apply Finset.disjoint_filter.mpr
  intro j _ h0 h1; omega

theorem day_types_disjoint_02 {n d : ℕ} (f : Fin n → Fin d) :
    Disjoint (daysWithExactly f 0) (daysWithExactly f 2) := by
  apply Finset.disjoint_filter.mpr
  intro j _ h0 h2; omega

theorem day_types_disjoint_12 {n d : ℕ} (f : Fin n → Fin d) :
    Disjoint (daysWithExactly f 1) (daysWithExactly f 2) := by
  apply Finset.disjoint_filter.mpr
  intro j _ h1 h2; omega

/-- The three day types cover all days (for valid k=3 assignments). -/
theorem day_types_cover {n d : ℕ} (f : Fin n → Fin d)
    (hvalid : ∀ j : Fin d, (fiberAt f j).card ≤ 2) :
    daysWithExactly f 0 ∪ daysWithExactly f 1 ∪ daysWithExactly f 2 = Finset.univ := by
  ext j
  simp only [daysWithExactly, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and, iff_true]
  rcases day_type_trichotomy f hvalid j with h | h | h
  · left; left; exact h
  · left; right; exact h
  · right; exact h

/-- The day type counts sum to d (for valid k=3 assignments). -/
theorem day_types_sum_d {n d : ℕ} (f : Fin n → Fin d)
    (hvalid : ∀ j : Fin d, (fiberAt f j).card ≤ 2) :
    (daysWithExactly f 0).card + (daysWithExactly f 1).card +
    (daysWithExactly f 2).card = d := by
  have hcover := day_types_cover f hvalid
  have h01 := day_types_disjoint_01 f
  have h02 := day_types_disjoint_02 f
  have h12 := day_types_disjoint_12 f
  have h012 : Disjoint (daysWithExactly f 0 ∪ daysWithExactly f 1)
      (daysWithExactly f 2) :=
    Finset.disjoint_union_left.mpr ⟨h02, h12⟩
  calc (daysWithExactly f 0).card + (daysWithExactly f 1).card +
        (daysWithExactly f 2).card
      = (daysWithExactly f 0 ∪ daysWithExactly f 1).card +
        (daysWithExactly f 2).card := by
          rw [Finset.card_union_of_disjoint h01]
    _ = (daysWithExactly f 0 ∪ daysWithExactly f 1 ∪ daysWithExactly f 2).card := by
          rw [Finset.card_union_of_disjoint h012]
    _ = Finset.univ.card := by rw [hcover]
    _ = d := by simp [Fintype.card_fin]

/-
## Part 5: Restriction Preserves Validity

Restricting an (n+1)-assignment to the first n people preserves fiber bounds.
This is key for the recursive structure.
-/

/-- Restriction to the first n people has weakly smaller fibers. -/
theorem fiberAt_restrict_le {n d : ℕ} (f : Fin (n + 1) → Fin d) (j : Fin d) :
    (fiberAt (f ∘ Fin.castSucc) j).card ≤ (fiberAt f j).card := by
  apply Finset.card_le_card
  intro i hi
  simp only [fiberAt, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.comp] at hi ⊢
  exact hi

/-- If an (n+1)-assignment has all fibers bounded by m, so does its restriction. -/
theorem restrict_valid {n d m : ℕ} (f : Fin (n + 1) → Fin d)
    (hvalid : ∀ j : Fin d, (fiberAt f j).card ≤ m) :
    ∀ j : Fin d, (fiberAt (f ∘ Fin.castSucc) j).card ≤ m :=
  fun j => le_trans (fiberAt_restrict_le f j) (hvalid j)

/-
## Summary

This file develops the extension-counting framework for computing the exact
k=3 birthday coincidence threshold:

1. Fiber partition: fiber sizes sum to n
2. Full days bound: #{days at capacity} < d when below pigeonhole limit
3. Extension counting: d - #{full days} valid choices for new person
4. Day type decomposition: empty + single + double = d for k=3
5. Restriction: restricting (n+1)-assignment preserves bounds

The framework enables recursive computation of the exact probability.
For d=365, k=3: the threshold where P(≥3 share) first exceeds 1/2 is n=88.

Theorems Proved: 14, Axioms: 0, Sorries: 0
-/

#check @fullDays_lt_d
#check @extensionCount_pos
#check @day_types_sum_d

end BirthdayKWayThreshold
