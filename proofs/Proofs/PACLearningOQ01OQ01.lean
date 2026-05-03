/-
  PAC Learning OQ-01 OQ-01: VC Dimension of Interval Classifiers on ℕ

  Interval classifiers on ℕ: h_{a,b} = { x | a ≤ x ∧ x ≤ b }.
  We prove VC dimension = 2:
  - Part I:  Interval classifiers shatter every 2-element set {a, b} with a < b.
  - Part II: Interval classifiers do NOT shatter any 3-element set {a, b, c} with a < b < c.

  The VC dimension = 2 result is the classical PAC learning example showing that interval
  classifiers are more expressive than threshold classifiers (VC dim 1) but strictly weaker
  than arbitrary classifiers.  Vapnik-Chervonenkis (1971); Blumer et al. (1989).
-/
import Mathlib
import Proofs.PACLearningOQ01

namespace LearningTheory.VCDimension

open Finset

/-- Interval classifiers on ℕ: h_{a,b} = { x | a ≤ x ∧ x ≤ b }.
    When a > b the set is empty, yielding the all-negative labeling. -/
def intervalClassifiers : Set (Set ℕ) :=
  { h | ∃ a b : ℕ, h = { x | a ≤ x ∧ x ≤ b } }

/-- Every 2-element set {a, b} (a < b) is shattered by interval classifiers.
    Witnesses: [a,b] for {a,b}, [a,a] for {a}, [b,b] for {b}, [b+1,b] for ∅. -/
theorem interval_shatters_pair (a b : ℕ) (hab : a < b) :
    Shatters intervalClassifiers ({a, b} : Finset ℕ) := by
  intro T _hT
  by_cases haT : a ∈ T <;> by_cases hbT : b ∈ T
  · -- T = {a, b}: use interval [a, b]
    refine ⟨{ y | a ≤ y ∧ y ≤ b }, ⟨a, b, rfl⟩, fun x hx => ?_⟩
    simp only [mem_insert, mem_singleton] at hx
    simp only [Set.mem_setOf_eq]
    rcases hx with ha | hb
    · subst ha; exact ⟨fun _ => haT, fun _ => ⟨le_refl a, hab.le⟩⟩
    · subst hb; exact ⟨fun _ => hbT, fun _ => ⟨hab.le, le_refl b⟩⟩
  · -- T = {a}: use interval [a, a]
    refine ⟨{ y | a ≤ y ∧ y ≤ a }, ⟨a, a, rfl⟩, fun x hx => ?_⟩
    simp only [mem_insert, mem_singleton] at hx
    simp only [Set.mem_setOf_eq]
    rcases hx with ha | hb
    · subst ha; exact ⟨fun _ => haT, fun _ => ⟨le_refl a, le_refl a⟩⟩
    · subst hb; exact ⟨fun ⟨_, hba⟩ => absurd hba (by omega), fun h => absurd h hbT⟩
  · -- T = {b}: use interval [b, b]
    refine ⟨{ y | b ≤ y ∧ y ≤ b }, ⟨b, b, rfl⟩, fun x hx => ?_⟩
    simp only [mem_insert, mem_singleton] at hx
    simp only [Set.mem_setOf_eq]
    rcases hx with ha | hb
    · subst ha; exact ⟨fun ⟨hbl, _⟩ => absurd hbl (by omega), fun h => absurd h haT⟩
    · subst hb; exact ⟨fun _ => hbT, fun _ => ⟨le_refl b, le_refl b⟩⟩
  · -- T = ∅: use empty interval [b+1, b]
    refine ⟨{ y | b + 1 ≤ y ∧ y ≤ b }, ⟨b + 1, b, rfl⟩, fun x hx => ?_⟩
    simp only [mem_insert, mem_singleton] at hx
    simp only [Set.mem_setOf_eq]
    rcases hx with ha | hb
    · subst ha; exact ⟨fun ⟨h, _⟩ => absurd h (by omega), fun h => absurd h haT⟩
    · subst hb; exact ⟨fun ⟨h, _⟩ => absurd h (by omega), fun h => absurd h hbT⟩

/-- No 3-element set {a, b, c} (a < b < c) is shattered by interval classifiers.
    Proof: the adversarial labeling {a, c} cannot be realized — any interval containing
    a and c must also contain b, since l ≤ a < b < c ≤ r forces l ≤ b ≤ r. -/
theorem interval_not_shatters_triple (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    ¬ Shatters intervalClassifiers ({a, b, c} : Finset ℕ) := by
  intro hShatter
  -- Adversarial labeling: include a and c, exclude b
  have hSub : ({a, c} : Finset ℕ) ⊆ ({a, b, c} : Finset ℕ) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx ⊢
    rcases hx with ha | hc
    · left; exact ha
    · right; right; exact hc
  obtain ⟨_, ⟨l, r, rfl⟩, hh⟩ := hShatter ({a, c} : Finset ℕ) hSub
  have ha_mem : a ∈ ({a, b, c} : Finset ℕ) := by simp
  have hb_mem : b ∈ ({a, b, c} : Finset ℕ) := by simp
  have hc_mem : c ∈ ({a, b, c} : Finset ℕ) := by simp
  have ha_T : a ∈ ({a, c} : Finset ℕ) := by simp
  have hb_T : b ∉ ({a, c} : Finset ℕ) := by
    simp only [mem_insert, mem_singleton]; omega
  have hc_T : c ∈ ({a, c} : Finset ℕ) := by simp
  -- a and c are in the interval [l, r]
  have ha_in : l ≤ a ∧ a ≤ r := by
    have h := (hh a ha_mem).mpr ha_T
    rw [Set.mem_setOf_eq] at h; exact h
  have hc_in : l ≤ c ∧ c ≤ r := by
    have h := (hh c hc_mem).mpr hc_T
    rw [Set.mem_setOf_eq] at h; exact h
  -- b is not in the interval [l, r]
  have hb_not : ¬ (l ≤ b ∧ b ≤ r) := by
    intro hb_in
    exact hb_T ((hh b hb_mem).mp (by rw [Set.mem_setOf_eq]; exact hb_in))
  -- But l ≤ a < b < c ≤ r forces b ∈ [l, r]: contradiction
  obtain ⟨hl_a, _⟩ := ha_in
  obtain ⟨_, hc_r⟩ := hc_in
  exact hb_not ⟨by omega, by omega⟩

/-- VC dimension of interval classifiers on ℕ is exactly 2:
    every 2-element set is shattered, but no 3-element set is. -/
theorem interval_vcdim_two :
    (∀ a b : ℕ, a < b → Shatters intervalClassifiers ({a, b} : Finset ℕ)) ∧
    (∀ a b c : ℕ, a < b → b < c → ¬ Shatters intervalClassifiers ({a, b, c} : Finset ℕ)) :=
  ⟨interval_shatters_pair, interval_not_shatters_triple⟩

end LearningTheory.VCDimension
