/-
  PAC Learning OQ-01 OQ-01: VC Dimension of Interval Classifiers on ℕ

  Interval classifiers on ℕ: H = { {x | a ≤ x ∧ x ≤ b} | a b : ℕ }
  (includes ∅ when a > b, since {x | a ≤ x ∧ x ≤ b} = ∅ whenever a > b).

  Main results:
  1. H shatters every 2-element set {p, q} with p < q → VCDim(H) ≥ 2
  2. H cannot shatter any 3-element set {a, b, c} with a < b < c → VCDim(H) ≤ 2
  Combined: VCDim(interval classifiers on ℕ) = 2.

  Proof of the obstruction: any interval containing the outer points a and c of a
  triple a < b < c must contain the middle point b by transitivity. So the labeling
  {a, c} (skipping b) is not achievable.

  Vapnik-Chervonenkis (1971). Classical result in learning theory.
-/
import Mathlib
import Proofs.PACLearningOQ01

namespace LearningTheory.VCDimension.Intervals

open Finset

/-- Interval classifiers on ℕ: all sets of the form [a, b] = {x | a ≤ x ∧ x ≤ b}.
    When a > b, the interval is empty (e.g., [q+1, q] = ∅).
    This hypothesis class has VC dimension exactly 2. -/
def intervalClassifiers : Set (Set ℕ) :=
  { h | ∃ a b : ℕ, h = {x | a ≤ x ∧ x ≤ b} }

/-- **Interval classifiers shatter every 2-element set**.
    For {p, q} with p < q, every subset is realized by an interval:
    - ∅: [q+1, q] (empty interval, since q+1 > q)
    - {p}: [p, p] (singleton)
    - {q}: [q, q] (singleton)
    - {p, q}: [p, q]
    Hence VCDim(intervalClassifiers) ≥ 2. -/
theorem interval_shatters_pair (p q : ℕ) (hpq : p < q) :
    Shatters intervalClassifiers ({p, q} : Finset ℕ) := by
  intro T hT
  by_cases hp : p ∈ T <;> by_cases hq : q ∈ T
  · -- T ⊇ {p, q}: use [p, q]
    refine ⟨{x | p ≤ x ∧ x ≤ q}, ⟨p, q, rfl⟩, ?_⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [Set.mem_setOf_eq]
      exact ⟨fun _ => hp, fun _ => ⟨le_refl p, le_of_lt hpq⟩⟩
    · rw [Set.mem_setOf_eq]
      exact ⟨fun _ => hq, fun _ => ⟨le_of_lt hpq, le_refl q⟩⟩
  · -- p ∈ T, q ∉ T: use [p, p]
    refine ⟨{x | p ≤ x ∧ x ≤ p}, ⟨p, p, rfl⟩, ?_⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [Set.mem_setOf_eq]
      exact ⟨fun _ => hp, fun _ => ⟨le_refl p, le_refl p⟩⟩
    · rw [Set.mem_setOf_eq]
      exact ⟨fun h => absurd h.2 (by omega), fun hq' => absurd hq' hq⟩
  · -- p ∉ T, q ∈ T: use [q, q]
    refine ⟨{x | q ≤ x ∧ x ≤ q}, ⟨q, q, rfl⟩, ?_⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [Set.mem_setOf_eq]
      exact ⟨fun h => absurd h.1 (by omega), fun hp' => absurd hp' hp⟩
    · rw [Set.mem_setOf_eq]
      exact ⟨fun _ => hq, fun _ => ⟨le_refl q, le_refl q⟩⟩
  · -- p ∉ T, q ∉ T: use [q+1, q] = ∅
    refine ⟨{x | q + 1 ≤ x ∧ x ≤ q}, ⟨q + 1, q, rfl⟩, ?_⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [Set.mem_setOf_eq]
      exact ⟨fun h => absurd h.1 (by omega), fun hp' => absurd hp' hp⟩
    · rw [Set.mem_setOf_eq]
      exact ⟨fun h => absurd h.1 (by omega), fun hq' => absurd hq' hq⟩

/-- **Interval classifiers cannot shatter any 3-element set**.
    For {a, b, c} with a < b < c, the labeling {a, c} (selecting outer points,
    skipping the middle) cannot be achieved: any interval [lo, hi] containing a
    and c must also contain b (since lo ≤ a < b < c ≤ hi forces lo ≤ b ≤ hi).
    Hence VCDim(intervalClassifiers) ≤ 2. -/
theorem interval_not_shatters_triple (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    ¬ Shatters intervalClassifiers ({a, b, c} : Finset ℕ) := by
  intro hShatter
  -- {a, c} ⊆ {a, b, c}
  have hAC_sub : ({a, c} : Finset ℕ) ⊆ ({a, b, c} : Finset ℕ) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx ⊢
    rcases hx with rfl | rfl
    · left; rfl
    · right; right; rfl
  -- Obtain interval [lo, hi] witnessing T = {a, c}
  obtain ⟨_, ⟨lo, hi, rfl⟩, hh⟩ := hShatter ({a, c} : Finset ℕ) hAC_sub
  -- a, b, c all belong to the ambient set {a, b, c}
  have ha_mem : a ∈ ({a, b, c} : Finset ℕ) := by simp
  have hb_mem : b ∈ ({a, b, c} : Finset ℕ) := by simp
  have hc_mem : c ∈ ({a, b, c} : Finset ℕ) := by simp
  -- a ∈ [lo, hi] since a ∈ {a, c}
  have ha_in : lo ≤ a ∧ a ≤ hi := by
    have hmem := (hh a ha_mem).mpr (by simp)
    rwa [Set.mem_setOf_eq] at hmem
  -- c ∈ [lo, hi] since c ∈ {a, c}
  have hc_in : lo ≤ c ∧ c ≤ hi := by
    have hmem := (hh c hc_mem).mpr (by simp)
    rwa [Set.mem_setOf_eq] at hmem
  -- b ∉ {a, c} (since a < b and b < c)
  have hb_notin_ac : b ∉ ({a, c} : Finset ℕ) := by
    simp only [mem_insert, mem_singleton, not_or]
    constructor <;> omega
  -- Therefore b ∉ [lo, hi]
  have hb_not : ¬(lo ≤ b ∧ b ≤ hi) := by
    intro hb_in
    exact hb_notin_ac ((hh b hb_mem).mp (by rwa [Set.mem_setOf_eq]))
  -- But lo ≤ a < b and b < c ≤ hi forces b ∈ [lo, hi]: contradiction
  exact hb_not ⟨le_trans ha_in.1 (le_of_lt hab), le_trans (le_of_lt hbc) hc_in.2⟩

/-- **Combined VC dimension bounds for interval classifiers on ℕ**.
    Part 1: Every pair {p, q} with p < q is shattered (VCDim ≥ 2).
    Part 2: No ordered triple {a, b, c} with a < b < c is shattered (VCDim ≤ 2).
    Together these establish VCDim(intervalClassifiers) = 2. -/
theorem interval_vcdim_bounds :
    (∀ p q : ℕ, p < q → Shatters intervalClassifiers ({p, q} : Finset ℕ)) ∧
    (∀ a b c : ℕ, a < b → b < c →
      ¬ Shatters intervalClassifiers ({a, b, c} : Finset ℕ)) :=
  ⟨interval_shatters_pair, interval_not_shatters_triple⟩

end LearningTheory.VCDimension.Intervals
