/-
# Erdős Problem #882 — OQ-03: Structural theory of valid subset-sum sets

Erdős Problem #882 asks for the largest `A ⊆ {1,…,n}` whose non-empty subset
sums are pairwise non-dividing (answer: `(1+o(1)) log₂ n`).  The parent file
`Erdos882Problem` introduces the concrete predicates `subsetSums`,
`DivisibilityFree`, `ValidSubset` and states the two deep analytic bounds as
axioms, but proves *no* structural properties of the predicates.

This file supplies that missing structural layer — all fully machine-checked
(0 axioms, 0 sorries):

  * `subsetSums_mono`         — subset sums grow with the set;
  * `DivisibilityFree.mono`   — divisibility-freeness is hereditary;
  * `validSubset_subset`      — **`ValidSubset` is downward closed**;
  * `subsetSums_nonempty`     — a non-empty set has a non-empty sum set;
  * `subsetSums_pos`          — subset sums of positive sets are positive.

The headline is downward closure: any subset of a valid set is valid — the
standard "WLOG pass to a sub-configuration" tool for extremal arguments, and
the exact monotonicity the upper-bound proof leans on.

Self-contained: the four predicates are re-declared here (the parent file
predates the current Mathlib toolchain and no longer builds), using the modern
Finset API, so this contribution stands on its own.

Reference: Erdős Problem #882, https://erdosproblems.com/882
-/

import Mathlib

namespace Erdos882OQ03

open Finset BigOperators

/-- All non-empty subsets of a finite set. -/
def nonemptySubsets (A : Finset ℕ) : Finset (Finset ℕ) :=
  A.powerset.filter (· ≠ ∅)

/-- The set of all non-empty subset sums `{∑_{a ∈ S} a : ∅ ≠ S ⊆ A}`. -/
def subsetSums (A : Finset ℕ) : Finset ℕ :=
  (nonemptySubsets A).image (fun S => S.sum id)

/-- No two distinct elements of a set divide each other. -/
def DivisibilityFree (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬(a ∣ b) ∧ ¬(b ∣ a)

/-- `A` is a valid subset of `{1,…,n}` with divisibility-free subset sums. -/
def ValidSubset (n : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) ∧ DivisibilityFree (subsetSums A)

/-- Subset sums are monotone: enlarging `A` only adds subset sums.
    Every non-empty `S ⊆ A` is also a non-empty subset of `B ⊇ A`. -/
theorem subsetSums_mono {A B : Finset ℕ} (h : A ⊆ B) :
    subsetSums A ⊆ subsetSums B := by
  intro s hs
  unfold subsetSums nonemptySubsets at hs ⊢
  rw [Finset.mem_image] at hs ⊢
  obtain ⟨S, hS, rfl⟩ := hs
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  refine ⟨S, ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hS.1.trans h, hS.2⟩

/-- Divisibility-freeness is hereditary: a subset of a divisibility-free set is
    divisibility-free. -/
theorem DivisibilityFree.mono {S T : Finset ℕ} (h : S ⊆ T)
    (hT : DivisibilityFree T) : DivisibilityFree S :=
  fun a ha b hb hab => hT a (h ha) b (h hb) hab

/-- **`ValidSubset` is downward closed.**  Any subset `B` of a valid set `A`
    is itself valid: the membership bounds restrict, and the divisibility-free
    condition on `subsetSums B ⊆ subsetSums A` is inherited. -/
theorem validSubset_subset {n : ℕ} {A B : Finset ℕ}
    (hA : ValidSubset n A) (h : B ⊆ A) : ValidSubset n B := by
  obtain ⟨hbound, hdf⟩ := hA
  exact ⟨fun a ha => hbound a (h ha), hdf.mono (subsetSums_mono h)⟩

/-- A non-empty set has at least one non-empty subset sum (e.g. a singleton). -/
theorem subsetSums_nonempty {A : Finset ℕ} (hA : A.Nonempty) :
    (subsetSums A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  refine ⟨a, ?_⟩
  unfold subsetSums nonemptySubsets
  rw [Finset.mem_image]
  refine ⟨{a}, ?_, by simp⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.singleton_subset_iff.mpr ha, Finset.singleton_ne_empty a⟩

/-- Every subset sum of a set of positive integers is itself positive: a
    non-empty subset of positive numbers sums to at least its smallest member. -/
theorem subsetSums_pos {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) :
    ∀ s ∈ subsetSums A, 1 ≤ s := by
  intro s hs
  unfold subsetSums nonemptySubsets at hs
  rw [Finset.mem_image] at hs
  obtain ⟨S, hS, rfl⟩ := hs
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSsub, hSne⟩ := hS
  obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hSne
  calc 1 ≤ b := hA b (hSsub hb)
    _ ≤ S.sum id := Finset.single_le_sum (fun i _ => Nat.zero_le (id i)) hb

end Erdos882OQ03
