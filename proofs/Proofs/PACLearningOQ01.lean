/-
  PAC Learning OQ-01: VC Dimension of Specific Hypothesis Classes

  Concrete VC dimension calculations for tractable hypothesis classes,
  advancing pac-learning-bounds-oq-01.

  - Part I: Shatters definition (Set-based, matching standard formulation).
  - Part II: Threshold classifiers on ℕ have VC dim ≥ 1 (shatter singletons).
  - Part III: Threshold classifiers on ℕ do NOT shatter any pair (VC dim ≤ 1).
  - Together: VC dim of thresholds on ℕ equals 1.

  Vapnik-Chervonenkis (1971).
-/
import Mathlib

namespace LearningTheory.VCDimension

open Finset

/-- A hypothesis class `H ⊆ Set α` shatters a finite set `S ⊆ α` if every
    subset `T ⊆ S` can be realized as `h ∩ S` for some `h ∈ H`. -/
def Shatters {α : Type*} (H : Set (Set α)) (S : Finset α) : Prop :=
  ∀ T : Finset α, T ⊆ S → ∃ h ∈ H, ∀ x ∈ S, (x ∈ h ↔ x ∈ T)

/-- Threshold classifiers on `ℕ`: `h_t = { x | x < t }`. -/
def thresholdClassifiers : Set (Set ℕ) :=
  { h | ∃ t : ℕ, h = { x | x < t } }

/-- Thresholds shatter every singleton: pick `t = a + 1` to include `a`,
    `t = 0` to exclude `a`. Hence VC dim of thresholds is at least 1. -/
theorem threshold_shatters_singleton (a : ℕ) :
    Shatters thresholdClassifiers ({a} : Finset ℕ) := by
  intro T _
  by_cases ha : a ∈ T
  · -- Include a: use threshold a + 1.
    refine ⟨{x | x < a + 1}, ⟨a + 1, rfl⟩, ?_⟩
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    refine ⟨fun _ => ha, fun _ => ?_⟩
    exact Nat.lt_succ_self x
  · -- Exclude a: use threshold 0.
    refine ⟨{x | x < 0}, ⟨0, rfl⟩, ?_⟩
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact absurd h (Nat.not_lt_zero x)
    · exact absurd h ha

/-- Thresholds cannot shatter any 2-element set. Suppose `a < b`; the labeling
    that selects only `b` (i.e. `T = {b}`) demands a threshold `t` with
    `t ≤ a` (to exclude a) and `b < t` (to include b), contradicting `a < b`. -/
theorem threshold_not_shatters_pair (a b : ℕ) (hab : a < b) :
    ¬ Shatters thresholdClassifiers ({a, b} : Finset ℕ) := by
  intro hShatter
  -- The witness labeling: T = {b}.
  have hSub : ({b} : Finset ℕ) ⊆ ({a, b} : Finset ℕ) := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    simp
  obtain ⟨h, ⟨t, ht⟩, hh⟩ := hShatter ({b} : Finset ℕ) hSub
  subst ht
  have ha_mem : a ∈ ({a, b} : Finset ℕ) := by simp
  have hb_mem : b ∈ ({a, b} : Finset ℕ) := by simp
  have ha := hh a ha_mem
  have hb := hh b hb_mem
  -- ha : a < t ↔ a ∈ {b}
  -- hb : b < t ↔ b ∈ {b}
  have ha' : ¬ (a < t) := by
    intro h
    have hmem : a ∈ ({b} : Finset ℕ) := ha.mp h
    rw [Finset.mem_singleton] at hmem
    omega
  have hb' : b < t := hb.mpr (by simp)
  omega

/-- Combined: VC dim of threshold classifiers on `ℕ` is exactly 1
    (no 2-element set is shattered, but every singleton is). -/
theorem threshold_vcdim_bounds :
    (∀ a : ℕ, Shatters thresholdClassifiers ({a} : Finset ℕ)) ∧
    (∀ a b : ℕ, a ≠ b → ¬ Shatters thresholdClassifiers ({a, b} : Finset ℕ)) := by
  refine ⟨threshold_shatters_singleton, ?_⟩
  intro a b hab hShatter
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact threshold_not_shatters_pair a b hlt hShatter
  · -- {a, b} = {b, a}; reuse with arguments swapped.
    have heq : ({a, b} : Finset ℕ) = ({b, a} : Finset ℕ) := by
      ext x; simp [Or.comm]
    rw [heq] at hShatter
    exact threshold_not_shatters_pair b a hgt hShatter

end LearningTheory.VCDimension
