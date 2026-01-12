/-
Copyright (c) 2026 LeanGenius Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanGenius AI Research
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem #340: Greedy Sidon Sequence Growth

## Problem Statement

Let A = {1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, ...} be the greedy Sidon sequence,
constructed by iteratively including the smallest positive integer that preserves
the Sidon property (all pairwise sums are distinct).

**Conjecture**: For all ε > 0, |A ∩ {1,...,N}| ≫ N^(1/2 - ε)

**Best known**: |A ∩ {1,...,N}| ≥ Ω(N^(1/3))

## References

- [erdosproblems.com/340](https://www.erdosproblems.com/340)
- OEIS A005282: Mian-Chowla sequence
- Singer (1938): Perfect difference sets give h(N) ≥ (1-o(1))N^(1/2)

## Mathematical Background

A **Sidon set** (also called B₂ sequence) is a set A of positive integers such that
all pairwise sums a + b (with a ≤ b, a,b ∈ A) are distinct.

Equivalently: if a + b = c + d with a,b,c,d ∈ A and a ≤ b, c ≤ d, then a = c and b = d.

The **greedy Sidon sequence** starts with 1, then repeatedly adds the smallest positive
integer that maintains the Sidon property.
-/

open Finset Filter Set
open scoped Pointwise

namespace Erdos340

/-! ## Part 1: Sidon Set Definition -/

/-- A finite set A is a Sidon set if all pairwise sums are distinct.
    Equivalently: a + b = c + d with a ≤ b, c ≤ d implies (a,b) = (c,d). -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- Alternative characterization: the sumset A + A has no repeated elements. -/
def IsSidon' (A : Finset ℕ) : Prop :=
  (A + A).card = A.card * (A.card + 1) / 2

/-- Empty set is trivially Sidon. -/
theorem isSidon_empty : IsSidon ∅ := by
  intro a b c d ha
  simp at ha

/-- Singleton is Sidon. -/
theorem isSidon_singleton (n : ℕ) : IsSidon {n} := by
  intro a b c d ha hb hc hd hab hcd heq
  simp at ha hb hc hd
  constructor <;> omega

/-- Pair {a, b} with a < b is Sidon iff 2a ≠ a + b and a + b ≠ 2b
    (which is always true when a ≠ b). -/
theorem isSidon_pair {a b : ℕ} (h : a < b) : IsSidon ({a, b} : Finset ℕ) := by
  intro x y z w hx hy hz hw hxy hzw heq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz hw
  -- Case analysis on which elements x, y, z, w are
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;>
  constructor <;> omega

/-! ## Part 2: Basic Sidon Properties -/

/-- Subset of a Sidon set is Sidon. -/
theorem IsSidon.subset {A B : Finset ℕ} (hA : IsSidon A) (hBA : B ⊆ A) : IsSidon B := by
  intro a b c d ha hb hc hd hab hcd heq
  exact hA a b c d (hBA ha) (hBA hb) (hBA hc) (hBA hd) hab hcd heq

/-- Key lemma: In a Sidon set, all pairwise differences are distinct.
    If a - b = c - d with a > b, c > d, then (a,b) = (c,d).

    Proof: a - b = c - d implies a + d = c + b. Rewriting as d + a = b + c,
    the Sidon property on the pairs (d,a) and (b,c) forces d = b and a = c. -/
theorem IsSidon.diff_injective {A : Finset ℕ} (hA : IsSidon A)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : b < a) (hcd : d < c) (heq : a - b = c - d) : a = c ∧ b = d := by
  -- Key step: a - b = c - d with a > b, c > d implies a + d = c + b
  have h : a + d = c + b := by
    have h1 : a - b + b = a := Nat.sub_add_cancel (le_of_lt hab)
    have h2 : c - d + d = c := Nat.sub_add_cancel (le_of_lt hcd)
    calc a + d = (a - b + b) + d := by rw [h1]
      _ = (a - b) + (b + d) := by rw [Nat.add_assoc]
      _ = (c - d) + (b + d) := by rw [heq]
      _ = (c - d) + (d + b) := by rw [Nat.add_comm b d]
      _ = (c - d + d) + b := by rw [← Nat.add_assoc]
      _ = c + b := by rw [h2]
  -- Rewrite as d + a = b + c to apply Sidon
  have h' : d + a = b + c := by rw [Nat.add_comm d a, Nat.add_comm b c]; exact h
  -- Need d ≤ a and b ≤ c to apply Sidon to (d,a) and (b,c)
  -- Case analysis: if d > a or b > c, we get contradictions
  by_cases hda : d ≤ a
  · by_cases hbc : b ≤ c
    · -- Main case: d ≤ a and b ≤ c
      -- Sidon gives d = b and a = c
      have := hA d a b c hd ha hb hc hda hbc h'
      exact ⟨this.2, this.1.symm⟩
    · -- b > c case: leads to contradiction
      push_neg at hbc
      -- We have b < a, d < c, d ≤ a, c < b
      -- So d < c < b < a, meaning d < b < a and c < b
      -- Apply Sidon to (c, b) and (d, a): c + b = d + a
      have h'' : c + b = d + a := by rw [Nat.add_comm c b]; exact h'.symm
      have := hA c b d a hc hb hd ha (le_of_lt hbc) hda h''
      -- This gives c = d and b = a, but d < c and b < a: contradiction
      omega
  · -- d > a case: leads to contradiction
    push_neg at hda
    -- We have d > a, but also b < a, d < c
    -- Apply Sidon to (a, d) and (b, c) or similar
    by_cases hbc : b ≤ c
    · -- d > a, b ≤ c
      have h'' : a + d = b + c := by rw [Nat.add_comm] at h'; exact h'
      have := hA a d b c ha hd hb hc (le_of_lt hda) hbc h''
      -- This gives a = b and d = c, but b < a: contradiction
      omega
    · push_neg at hbc
      -- d > a, b > c: we have c < b < a and a < d < c, contradiction
      omega

/-! ### Ordered Pairs and Difference Sets -/

/-- The set of ordered pairs (a, b) with a < b from a finset A. -/
def orderedPairsLt (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  A.offDiag.filter (fun p => p.1 < p.2)

/-- The difference function on pairs. -/
def pairDiff : ℕ × ℕ → ℕ := fun p => p.2 - p.1

/-- For a Sidon set, the difference map is injective on ordered pairs. -/
theorem sidon_pairDiff_injective {A : Finset ℕ} (hA : IsSidon A) :
    Set.InjOn pairDiff (orderedPairsLt A : Set (ℕ × ℕ)) := by
  intro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
  simp only [orderedPairsLt, Finset.coe_filter, Finset.mem_offDiag,
    Set.mem_setOf_eq] at hab hcd
  obtain ⟨⟨ha, hb, _⟩, hlt_ab⟩ := hab
  obtain ⟨⟨hc, hd, _⟩, hlt_cd⟩ := hcd
  simp only [pairDiff] at heq
  -- Use diff_injective: if b - a = d - c with a < b, c < d, then (b, a) = (d, c)
  have := hA.diff_injective hb ha hd hc hlt_ab hlt_cd heq
  ext <;> omega

/-- The difference set of a Sidon set has cardinality equal to the number of ordered pairs. -/
theorem sidon_diffSet_card {A : Finset ℕ} (hA : IsSidon A) :
    (Finset.image pairDiff (orderedPairsLt A)).card = (orderedPairsLt A).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy heq
  exact sidon_pairDiff_injective hA hx hy heq

/-- The number of ordered pairs (a, b) with a < b in A is n(n-1)/2. -/
theorem orderedPairsLt_card (A : Finset ℕ) :
    (orderedPairsLt A).card = A.card * (A.card - 1) / 2 := by
  -- The offDiag has n(n-1) pairs, half with a < b and half with a > b
  -- On ℕ with linear order, this is exactly half
  sorry -- Requires more Mathlib infrastructure about partitioning offDiag

/-- All differences in a Sidon set are positive and bounded by max - min. -/
theorem sidon_diff_pos_bounded {A : Finset ℕ} (hne : A.Nonempty)
    {p : ℕ × ℕ} (hp : p ∈ orderedPairsLt A) :
    0 < pairDiff p ∧ pairDiff p ≤ A.max' hne - A.min' hne := by
  simp only [orderedPairsLt, Finset.mem_filter, Finset.mem_offDiag] at hp
  obtain ⟨⟨ha, hb, _⟩, hlt⟩ := hp
  constructor
  · simp only [pairDiff]; omega
  · simp only [pairDiff]
    have h1 : p.1 ≥ A.min' hne := Finset.min'_le A p.1 ha
    have h2 : p.2 ≤ A.max' hne := Finset.le_max' A p.2 hb
    omega

/-- For a Sidon set A with n elements, the largest element is at least n(n-1)/2.

    Proof idea: There are C(n,2) = n(n-1)/2 distinct positive differences.
    These are distinct positive integers, so the largest is ≥ n(n-1)/2.
    The largest difference = max(A) - min(A) ≥ n(n-1)/2.
    Since min(A) ≥ 0, we get max(A) ≥ n(n-1)/2. -/
theorem sidon_lower_bound (A : Finset ℕ) (hA : IsSidon A) (hne : A.Nonempty) :
    A.max' hne ≥ A.card * (A.card - 1) / 2 := by
  -- The proof uses a counting argument:
  -- 1. There are n(n-1)/2 ordered pairs with a < b
  -- 2. Their differences are distinct (by sidon_pairDiff_injective)
  -- 3. Each difference is a positive integer ≤ max(A)
  -- 4. So max(A) ≥ n(n-1)/2
  by_cases hcard : A.card ≤ 1
  · -- Trivial case: n ≤ 1 means n(n-1)/2 = 0
    have hpos : 0 < A.card := Finset.card_pos.mpr hne
    have heq1 : A.card = 1 := Nat.le_antisymm hcard hpos
    simp only [heq1, Nat.sub_self, Nat.mul_zero, Nat.zero_div, Nat.zero_le]
  · -- Nontrivial case: n ≥ 2
    push_neg at hcard
    -- The difference set has n(n-1)/2 distinct positive integers
    -- Each is ≤ max(A) - min(A) ≤ max(A) (since min(A) ≥ 0)
    -- By pigeonhole, max(A) ≥ n(n-1)/2
    sorry -- Requires orderedPairsLt_card and pigeonhole argument

/-- Upper bound: A Sidon subset of {1,...,N} has at most √N + O(N^(1/4)) elements. -/
theorem sidon_upper_bound (A : Finset ℕ) (hA : IsSidon A) (N : ℕ)
    (hAN : ∀ a ∈ A, a ≤ N) : A.card ≤ Nat.sqrt N + Nat.sqrt (Nat.sqrt N) + 1 := by
  sorry -- Erdős-Turán bound

/-! ## Part 3: Greedy Sidon Sequence Construction -/

/-- Check if adding n to A preserves the Sidon property (Prop version). -/
def CanAddProp (A : Finset ℕ) (n : ℕ) : Prop :=
  n ∉ A ∧ IsSidon (A ∪ {n})

/-- The greedy Sidon sequence exists and is unique.
    We axiomatize its values directly for computational efficiency. -/
axiom greedySidonSeq : ℕ → ℕ

/-- The greedy Sidon sequence starts at 1. -/
axiom greedySidonSeq_zero : greedySidonSeq 0 = 1

/-- The greedy Sidon sequence is strictly increasing. -/
axiom greedySidonSeq_strictMono : StrictMono greedySidonSeq

/-- The set of first n+1 terms is always Sidon. -/
axiom greedySidonSeq_isSidon (n : ℕ) :
  IsSidon (Finset.image greedySidonSeq (Finset.range (n + 1)))

/-- The greedy property: greedySidon(n+1) is the smallest value > greedySidon(n)
    that can be added while preserving Sidon. -/
axiom greedySidonSeq_greedy (n : ℕ) :
  ∀ m, greedySidonSeq n < m → m < greedySidonSeq (n + 1) →
    ¬IsSidon (Finset.image greedySidonSeq (Finset.range (n + 1)) ∪ {m})

/-- Alias for compatibility. -/
noncomputable def greedySidon : ℕ → ℕ := greedySidonSeq

/-- The first n+1 elements of the greedy Sidon sequence as a set. -/
noncomputable def greedySidonSet (n : ℕ) : Finset ℕ :=
  Finset.image greedySidon (Finset.range (n + 1))

/-! ## Part 4: Computational Verification -/

-- These would require decidable instances; marking as axioms for now
axiom greedySidon_0 : greedySidon 0 = 1
axiom greedySidon_1 : greedySidon 1 = 2
axiom greedySidon_2 : greedySidon 2 = 4
axiom greedySidon_3 : greedySidon 3 = 8
axiom greedySidon_4 : greedySidon 4 = 13
axiom greedySidon_5 : greedySidon 5 = 21
axiom greedySidon_6 : greedySidon 6 = 31
axiom greedySidon_7 : greedySidon 7 = 45
axiom greedySidon_8 : greedySidon 8 = 66
axiom greedySidon_9 : greedySidon 9 = 81
axiom greedySidon_10 : greedySidon 10 = 97

/-- The greedy Sidon sequence is strictly increasing. -/
theorem greedySidon_strictMono : StrictMono greedySidon :=
  greedySidonSeq_strictMono

/-- The greedy Sidon set is always a Sidon set. -/
theorem greedySidonSet_isSidon (n : ℕ) : IsSidon (greedySidonSet n) :=
  greedySidonSeq_isSidon n

/-! ## Part 5: Growth Rate Bounds -/

/-- Count of greedy Sidon elements up to N. -/
noncomputable def greedySidonCount (N : ℕ) : ℕ :=
  (Set.range greedySidon ∩ Set.Icc 1 N).ncard

/-- **Known Result**: The greedy Sidon sequence grows at least like N^(1/3).

This is the trivial lower bound from the greedy construction. -/
theorem greedySidon_growth_third :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1/3 : ℝ) ≤ C * (greedySidonCount N : ℝ) := by
  sorry

-- REMOVED FOR ARISTOTLE: erdos_340 is an OPEN conjecture (no known proof)
-- The main conjecture is our research target - work on it with Claude, not Aristotle
-- theorem erdos_340 (ε : ℝ) (hε : ε > 0) :
--     ∃ C : ℝ, C > 0 ∧ ∀ᶠ N : ℕ in atTop,
--       (N : ℝ) ^ ((1:ℝ)/2 - ε) ≤ C * (greedySidonCount N : ℝ) := by
--   sorry

/-! ## Part 6: Difference Set Properties -/

/-- The difference set A - A of the greedy Sidon sequence. -/
def greedySidonDiffSet : Set ℤ :=
  {d : ℤ | ∃ a b : ℕ, a ∈ Set.range greedySidon ∧ b ∈ Set.range greedySidon ∧ d = a - b}

/-- 22 is in the difference set: 204 - 182 = 22. -/
theorem _22_mem_diffSet : (22 : ℤ) ∈ greedySidonDiffSet := by
  sorry -- Computational verification

-- REMOVED FOR ARISTOTLE: Unknown if 33 is in the difference set
-- theorem _33_mem_diffSet_iff : 33 ∈ greedySidonDiffSet ↔ True := by
--   sorry -- Unknown

end Erdos340
