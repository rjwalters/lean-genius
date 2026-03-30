/-
  VC Dimension: Definitions and Computations

  Defines VC dimension for hypothesis classes and computes it for:
  1. Powerset (all subsets): shatters every finite set
  2. Threshold classifiers on ℕ: VCDim = 1 (shatters singletons, not pairs)
  3. Interval classifiers on ℕ: VCDim = 2 (shatters pairs, not triples)

  The interval non-shattering uses interval convexity: if a < b < c
  and both a,c ∈ [lo,hi), then b ∈ [lo,hi), so {a,c} is unrealizable.

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
-- PART 5: Interval VCDim = 2 (Non-Shattering of Triples)
-- ============================================================

/-- Key convexity lemma: If a < b < c and both a and c are in an interval
    [lo, hi), then b is also in the interval. This is the essential property
    that prevents intervals from shattering triples. -/
private lemma interval_convex (a b c lo hi : ℕ)
    (hab : a < b) (hbc : b < c)
    (ha : lo ≤ a ∧ a < hi) (hc : lo ≤ c ∧ c < hi) :
    lo ≤ b ∧ b < hi := by
  constructor <;> omega

/-- Interval classifiers cannot shatter any triple {a, b, c} with a < b < c.
    The subset {a, c} (containing a and c but not b) cannot be realized by
    any interval [lo, hi): if a ∈ [lo, hi) and c ∈ [lo, hi), then lo ≤ a < b < c < hi,
    so b ∈ [lo, hi) as well. This is the convexity of intervals. -/
theorem interval_not_shatters_triple (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    ¬Shatters intervalClassifiers {a, b, c} := by
  intro hsh
  -- Try to realize the subset {a, c} (a and c in, b out)
  have hac_sub : ({a, c} : Finset ℕ) ⊆ {a, b, c} := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx ⊢
    rcases hx with rfl | rfl <;> simp [*]
  obtain ⟨h, ⟨lo, hi, hh⟩, hchar⟩ := hsh {a, c} hac_sub
  -- a ∈ {a, c}, so a ∈ h
  have ha_in : a ∈ h := (hchar a (mem_insert_self a _)).mpr (mem_insert_self a _)
  -- c ∈ {a, c}, so c ∈ h
  have hc_in : c ∈ h :=
    (hchar c (by simp)).mpr (by simp [Finset.mem_insert, Finset.mem_singleton])
  -- b ∉ {a, c} (since a < b and b < c), so b ∉ h
  have hb_not : b ∉ h := by
    intro hb_in
    have hb_mem := (hchar b (by simp)).mp hb_in
    simp only [mem_insert, mem_singleton] at hb_mem
    rcases hb_mem with rfl | rfl <;> omega
  -- But a ∈ [lo, hi) and c ∈ [lo, hi) imply b ∈ [lo, hi) by convexity
  rw [hh, Set.mem_setOf_eq] at ha_in hc_in hb_not
  exact hb_not (interval_convex a b c lo hi hab hbc ha_in hc_in)

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

Threshold VCDim = 1: shatters singletons (threshold_shatters_singleton),
  cannot shatter pairs (threshold_not_shatters_pair).

Interval VCDim = 2: shatters pairs (interval_shatters_pair),
  cannot shatter triples (interval_not_shatters_triple).
  The non-shattering uses the convexity of intervals: if a < b < c and
  both a,c ∈ [lo,hi), then b ∈ [lo,hi), so {a,c} cannot be realized.
-/

#check @Shatters
#check @vcDim
#check @powerset_shatters
#check @threshold_shatters_singleton
#check @threshold_not_shatters_pair
#check @interval_shatters_pair
#check @interval_not_shatters_triple
