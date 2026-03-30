/-
  Aristotle targets for Erdős Problem #501
  Routine supporting lemmas for automated proof search.
  See Erdos501Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (monotonicity, subadditivity, etc.)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)

  These lemmas support the proof of erdos_hajnal_finite (Erdős-Hajnal 1960):
  "For any bounded outer measure family, arbitrarily large finite independent
  sets exist."

  Key proof approach: probabilistic counting / measure union bound
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OuterMeasure.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Tactic

namespace Erdos501Support

open Set MeasureTheory

/-- A set is bounded if it's contained in some interval [-M, M]. -/
def IsBoundedSet (A : Set ℝ) : Prop :=
  ∃ M : ℝ, A ⊆ Set.Icc (-M) M

/-- The outer measure of a set (Lebesgue). -/
noncomputable def outerMeasure (A : Set ℝ) : ℝ≥0∞ :=
  MeasureTheory.Measure.lebesgue.toOuterMeasure A

-- ============================================================
-- Supporting lemmas for erdos_hajnal_finite
-- ============================================================

/-- Empty set is bounded. -/
theorem bounded_empty : IsBoundedSet ∅ := by
  exact ⟨0, Set.empty_subset _⟩

/-- Subset of a bounded set is bounded. -/
theorem bounded_subset {A B : Set ℝ} (hA : IsBoundedSet A) (hB : B ⊆ A) :
    IsBoundedSet B := by
  obtain ⟨M, hM⟩ := hA
  exact ⟨M, hB.trans hM⟩

/-- Intersection with a closed interval is bounded. -/
theorem bounded_inter_Icc (A : Set ℝ) (a b : ℝ) :
    IsBoundedSet (A ∩ Set.Icc a b) := by
  refine ⟨max (|a|) (|b|), ?_⟩
  intro x ⟨_, hx⟩
  constructor
  · linarith [neg_abs_le a, hx.1]
  · linarith [le_abs_self b, hx.2]

/-- Union of two bounded sets is bounded. -/
theorem bounded_union {A B : Set ℝ} (hA : IsBoundedSet A) (hB : IsBoundedSet B) :
    IsBoundedSet (A ∪ B) := by
  obtain ⟨M₁, hM₁⟩ := hA
  obtain ⟨M₂, hM₂⟩ := hB
  refine ⟨max M₁ M₂, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · have := hM₁ hx
    constructor
    · linarith [this.1, neg_le_neg (le_max_left M₁ M₂)]
    · linarith [this.2, le_max_left M₁ M₂]
  · have := hM₂ hx
    constructor
    · linarith [this.1, neg_le_neg (le_max_right M₁ M₂)]
    · linarith [this.2, le_max_right M₁ M₂]

/-- Outer measure is monotone: A ⊆ B → μ*(A) ≤ μ*(B). -/
theorem outerMeasure_mono {A B : Set ℝ} (h : A ⊆ B) :
    outerMeasure A ≤ outerMeasure B := by
  exact MeasureTheory.measure_mono h

/-- Outer measure of a subset is at most that of the superset. -/
theorem outerMeasure_inter_le (A S : Set ℝ) :
    outerMeasure (A ∩ S) ≤ outerMeasure A := by
  exact outerMeasure_mono Set.inter_subset_left

/-- Subadditivity: μ*(A ∪ B) ≤ μ*(A) + μ*(B). -/
theorem outerMeasure_union_le (A B : Set ℝ) :
    outerMeasure (A ∪ B) ≤ outerMeasure A + outerMeasure B := by
  exact MeasureTheory.measure_union_le A B

/-- If a set has outer measure less than the length of an interval,
    then the interval is not contained in the set.
    Equivalently: some point in the interval is not in the set. -/
theorem exists_not_mem_of_outerMeasure_lt_Icc {A : Set ℝ} {a b : ℝ}
    (hab : a < b) (hA : outerMeasure A < ENNReal.ofReal (b - a)) :
    ∃ x ∈ Set.Icc a b, x ∉ A := by
  sorry

/-- A closed set in ℝ is Lebesgue measurable. -/
theorem isClosed_measurableSet {A : Set ℝ} (hA : IsClosed A) :
    MeasurableSet A := by
  exact hA.measurableSet

/-- For a closed set, outer measure equals Lebesgue measure. -/
theorem closed_outerMeasure_eq_measure {A : Set ℝ} (hA : IsClosed A) :
    outerMeasure A = MeasureTheory.Measure.lebesgue A := by
  rfl

/-- The complement of a closed set in an interval has positive measure
    when the closed set has measure less than the interval length. -/
theorem measure_compl_Icc_pos {A : Set ℝ} {a b : ℝ}
    (hA : IsClosed A) (hab : a < b)
    (hμ : outerMeasure A < ENNReal.ofReal (b - a)) :
    0 < outerMeasure (Set.Icc a b \ A) := by
  sorry

/-- An independent set of size 0 exists for any family. -/
theorem independent_size_zero (A : ℝ → Set ℝ) :
    ∃ X : Finset ℝ, X.card = 0 ∧ ∀ x ∈ (↑X : Set ℝ), ∀ y ∈ (↑X : Set ℝ),
      x ≠ y → x ∉ A y := by
  exact ⟨∅, rfl, fun x hx => (Finset.not_mem_empty x hx).elim⟩

/-- An independent set of size 1 exists for any family. -/
theorem independent_size_one (A : ℝ → Set ℝ) :
    ∃ X : Finset ℝ, X.card = 1 ∧ ∀ x ∈ (↑X : Set ℝ), ∀ y ∈ (↑X : Set ℝ),
      x ≠ y → x ∉ A y := by
  refine ⟨{0}, Finset.card_singleton 0, ?_⟩
  intro x hx y hy hxy
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
  subst hx; subst hy
  exact absurd rfl hxy

end Erdos501Support
