/-
  VC Dimension: Definitions and Computations

  Defines VC dimension for hypothesis classes and computes it for:
  1. Powerset (all subsets): shatters every finite set
  2. Threshold classifiers on ℕ: VCDim = 1 (shatters singletons, not pairs)
  3. Interval classifiers on ℕ: VCDim ≥ 2 (shatters pairs)

  Vapnik-Chervonenkis (1971)

  This extends PACLearning.lean which proves the Sauer-Shelah lemma
  and PAC sample complexity bounds.
-/
import Mathlib

namespace VCDimension

open Finset

-- ============================================================
-- PART 1: Core Definitions
-- ============================================================

/-- A hypothesis class is a family of subsets of α. -/
abbrev HypothesisClass (α : Type*) := Set (Set α)

/-- H shatters S if every subset of S is realized as the intersection
    with some hypothesis h ∈ H. -/
def Shatters {α : Type*} (H : HypothesisClass α) (S : Finset α) : Prop :=
  ∀ T : Finset α, T ⊆ S → ∃ h ∈ H, ∀ x ∈ S, (x ∈ h ↔ x ∈ T)

/-- The VC dimension is the size of the largest shattered set. -/
noncomputable def vcDim {α : Type*} (H : HypothesisClass α) : ℕ :=
  sSup {n : ℕ | ∃ S : Finset α, S.card = n ∧ Shatters H S}

-- ============================================================
-- PART 2: Powerset (All Subsets)
-- ============================================================

/-- The powerset hypothesis class: all subsets of Ω. -/
def powerset (Ω : Type*) : HypothesisClass Ω := Set.univ

/-- The powerset shatters every finite set: for any T ⊆ S,
    use h = ↑T ∈ Set.univ. -/
theorem powerset_shatters {Ω : Type*} (S : Finset Ω) :
    Shatters (powerset Ω) S := by
  intro T _
  exact ⟨↑T, Set.mem_univ _, fun x _ => Iff.rfl⟩

-- ============================================================
-- PART 3: Threshold Classifiers
-- ============================================================

/-- Threshold classifier on ℕ: {n | n < t} for each threshold t.
    Includes ∅ (t = 0) and arbitrarily large initial segments. -/
def thresholdClassifiers : HypothesisClass ℕ :=
  {h | ∃ t : ℕ, h = {n : ℕ | n < t}}

/-- Threshold classifiers shatter any singleton {a}:
    ∅ via threshold 0, and {a} via threshold a+1. -/
theorem threshold_shatters_singleton (a : ℕ) :
    Shatters thresholdClassifiers {a} := by
  intro T hT
  by_cases ha : a ∈ T
  · -- T = {a}: use threshold a+1
    have hTeq : T = {a} := eq_singleton_iff_unique_mem.mpr
      ⟨ha, fun x hx => mem_singleton.mp (hT hx)⟩
    exact ⟨{n | n < a + 1}, ⟨a + 1, rfl⟩, fun x hx => by
      rw [mem_singleton.mp hx, hTeq]; simp [Nat.lt_succ_iff]⟩
  · -- T = ∅: use threshold 0
    have hTeq : T = ∅ := by
      ext x; simp only [not_mem_empty, iff_false]
      exact fun hx => ha (by rwa [mem_singleton.mp (hT hx)])
    exact ⟨{n | n < 0}, ⟨0, rfl⟩, fun x hx => by
      rw [mem_singleton.mp hx, hTeq]; simp⟩

/-- Threshold classifiers cannot shatter {a, b} with a < b.
    The subset {b} requires b ∈ h and a ∉ h, but for h = {n | n < t},
    b < t forces a < t (since a < b), contradicting a ∉ h. -/
theorem threshold_not_shatters_pair (a b : ℕ) (hab : a < b) :
    ¬Shatters thresholdClassifiers {a, b} := by
  intro hsh
  -- Realize the subset {b}: b in, a out
  obtain ⟨h, ⟨t, ht⟩, hchar⟩ := hsh {b} (by simp)
  -- b ∈ h ↔ b ∈ {b}, so b ∈ h
  have hb : b ∈ h := (hchar b (by simp)).mpr (by simp)
  -- a ∈ h ↔ a ∈ {b}, and a ≠ b, so a ∉ h
  have ha : a ∉ h := by
    intro ha_in
    have := (hchar a (by simp)).mp ha_in
    simp at this -- a ∈ {b} means a = b
    omega -- contradicts a < b
  -- b ∈ h means b < t, and a ∉ h means ¬(a < t), i.e., t ≤ a
  rw [ht, Set.mem_setOf_eq] at hb
  rw [ht, Set.mem_setOf_eq] at ha
  push_neg at ha
  -- t ≤ a < b < t is impossible
  omega

-- ============================================================
-- PART 4: Interval Classifiers
-- ============================================================

/-- Interval classifier on ℕ: {n | lo ≤ n ∧ n < hi}. -/
def intervalClassifiers : HypothesisClass ℕ :=
  {h | ∃ lo hi : ℕ, h = {n : ℕ | lo ≤ n ∧ n < hi}}

/-- Interval classifiers shatter any pair {a, b} with a < b.
    The four subsets ∅, {a}, {b}, {a,b} are realized by appropriate intervals. -/
theorem interval_shatters_pair (a b : ℕ) (hab : a < b) :
    Shatters intervalClassifiers {a, b} := by
  intro T hT
  by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
  · -- T = {a, b}: interval [a, b+1)
    exact ⟨{n | a ≤ n ∧ n < b + 1}, ⟨a, b + 1, rfl⟩, fun x hx => by
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp only [Set.mem_setOf_eq]; constructor <;> intro _ <;> omega
      · simp only [Set.mem_setOf_eq]; constructor <;> intro _ <;> omega⟩
  · -- T = {a}: interval [a, a+1)
    exact ⟨{n | a ≤ n ∧ n < a + 1}, ⟨a, a + 1, rfl⟩, fun x hx => by
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp only [Set.mem_setOf_eq]; constructor <;> intro _ <;> omega
      · simp only [Set.mem_setOf_eq]; constructor
        · intro ⟨_, hlt⟩; omega
        · intro hmem; exact absurd hmem hb⟩
  · -- T = {b}: interval [b, b+1)
    exact ⟨{n | b ≤ n ∧ n < b + 1}, ⟨b, b + 1, rfl⟩, fun x hx => by
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp only [Set.mem_setOf_eq]; constructor
        · intro ⟨hle, _⟩; omega
        · intro hmem; exact absurd hmem ha
      · simp only [Set.mem_setOf_eq]; constructor <;> intro _ <;> omega⟩
  · -- T = ∅: empty interval [0, 0)
    have hTeq : T = ∅ := by
      ext x; simp only [not_mem_empty, iff_false]
      intro hx; have := hT hx
      simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl <;> contradiction
    exact ⟨{n | (0 : ℕ) ≤ n ∧ n < 0}, ⟨0, 0, rfl⟩, fun x hx => by
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [hTeq, Set.mem_setOf_eq] <;> omega⟩

-- ============================================================
-- PART 5: Interval Convexity and VCDim = 2
-- ============================================================

/-- Key structural property: intervals are convex. If a ∈ [lo,hi) and
    c ∈ [lo,hi) with a ≤ b ≤ c, then b ∈ [lo,hi). -/
lemma interval_convex {lo hi a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (ha : lo ≤ a ∧ a < hi) (hc : lo ≤ c ∧ c < hi) :
    lo ≤ b ∧ b < hi := by
  exact ⟨le_trans ha.1 hab, lt_of_le_of_lt hbc hc.2⟩

/-- Interval classifiers cannot shatter {a, b, c} with a < b < c.
    The subset {a, c} requires a ∈ h, c ∈ h, b ∉ h. But for any
    interval h = [lo, hi), if a,c ∈ h then lo ≤ a < b < c < hi,
    so b ∈ h by convexity — contradiction. -/
theorem interval_not_shatters_triple (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    ¬Shatters intervalClassifiers {a, b, c} := by
  intro hsh
  -- Realize the subset {a, c}: a in, b out, c in
  have hac_sub : ({a, c} : Finset ℕ) ⊆ {a, b, c} := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto
  obtain ⟨h, ⟨lo, hi, hh⟩, hchar⟩ := hsh {a, c} hac_sub
  -- hchar : ∀ x ∈ {a, b, c}, (x ∈ h ↔ x ∈ {a, c})
  have ha_in : a ∈ h := (hchar a (by simp)).mpr (by simp)
  have hc_in : c ∈ h := (hchar c (by simp)).mpr (by simp)
  have hb_not : b ∉ h := by
    intro hb_in
    have hmem := (hchar b (by simp)).mp hb_in
    -- b ∈ {a, c} means b = a or b = c, contradicting a < b < c
    simp only [mem_insert, mem_singleton] at hmem; omega
  -- h = [lo, hi), a ∈ h and c ∈ h imply b ∈ h by interval convexity
  rw [hh, Set.mem_setOf_eq] at ha_in hc_in hb_not
  exact hb_not (interval_convex (Nat.le_of_lt hab) (Nat.le_of_lt hbc) ha_in hc_in)

-- ============================================================
-- PART 6: Summary
-- ============================================================

/-
## Results Summary

| Hypothesis Class       | Shatters          | Doesn't Shatter | VCDim |
|------------------------|-------------------|------------------|-------|
| Powerset (all subsets) | all finite sets   | -                | |Ω|   |
| Threshold classifiers  | singletons        | pairs            | 1     |
| Interval classifiers   | pairs             | triples          | 2     |
-/

end VCDimension
