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
  by_contra h
  push_neg at h
  -- h : Icc a b ⊆ A
  have hIcc : outerMeasure (Set.Icc a b) = ENNReal.ofReal (b - a) := by
    unfold outerMeasure; exact Real.volume_Icc
  exact absurd hA (not_lt.mpr (hIcc ▸ outerMeasure_mono h))

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
  obtain ⟨x, hx_mem, hx_notin⟩ := exists_not_mem_of_outerMeasure_lt_Icc hab hμ
  -- x ∈ Aᶜ which is open, so ∃ ε > 0 with ball x ε ⊆ Aᶜ
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hA.isOpen_compl x hx_notin
  -- Build [lo, hi] ⊆ [a,b] \ A with positive length
  set lo := max a (x - ε / 2)
  set hi := min b (x + ε / 2)
  have hlo_hi : lo < hi := by
    simp only [lo, hi, lt_min_iff, max_lt_iff]
    exact ⟨⟨by linarith [hx_mem.2], by linarith⟩,
           ⟨by linarith [hx_mem.1], by linarith⟩⟩
  have h_sub : Set.Icc lo hi ⊆ Set.Icc a b \ A := by
    intro y hy
    refine ⟨⟨le_of_max_le_left hy.1, le_trans hy.2 (min_le_left _ _)⟩, ?_⟩
    apply hε_ball
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [le_of_max_le_right hy.1], by linarith [le_trans hy.2 (min_le_right _ _)]⟩
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (hi - lo) := by rwa [ENNReal.ofReal_pos, sub_pos]
    _ = outerMeasure (Set.Icc lo hi) := by
        symm; unfold outerMeasure; exact Real.volume_Icc
    _ ≤ outerMeasure (Set.Icc a b \ A) := outerMeasure_mono h_sub

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
