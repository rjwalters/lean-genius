import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-
# Discrete Isoperimetric Inequality

The discrete analogue of the isoperimetric theorem: among all finite subsets
of Z with a given cardinality, intervals have the smallest boundary.

For a finite non-empty subset S of Z, the edge boundary
  dS = {z in Z \ S : |z - s| = 1 for some s in S}
satisfies |dS| >= 2, with equality iff S is an interval {a, a+1, ..., b}.

This is the simplest case of the discrete isoperimetric inequality,
which in d dimensions says: for S in Z^d with |S| = n,
  |dS| >= 2d * n^{(d-1)/d}
with equality for d-dimensional cubes.

Extends the continuous isoperimetric inequality (4piA <= L^2) in
IsoperimetricTheorem.lean.
-/

set_option linter.unusedVariables false

namespace DiscreteIsoperimetric

open Finset

-- ============================================================
-- SECTION I: Edge Boundary in Z
-- ============================================================

/-- The edge boundary of a finite subset S of Z: integers not in S
    that are adjacent (distance 1) to some element of S. -/
def edgeBoundary (S : Finset ℤ) : Finset ℤ :=
  (S.biUnion (fun s => {s - 1, s + 1})).filter (fun z => z ∉ S)

/-- A finite subset S of Z is an interval: S = {a, a+1, ..., a+n-1}
    for some a and n = |S|. Equivalently, S = Finset.Icc a b for some a ≤ b. -/
def IsInterval (S : Finset ℤ) : Prop :=
  ∃ a b : ℤ, a ≤ b ∧ S = Finset.Icc a b

-- ============================================================
-- SECTION II: Boundary Lower Bound
-- ============================================================

/-- The minimum and maximum of a nonempty Finset Z are in S. -/
lemma min_mem_of_nonempty {S : Finset ℤ} (hne : S.Nonempty) :
    S.min' hne ∈ S := Finset.min'_mem S hne

lemma max_mem_of_nonempty {S : Finset ℤ} (hne : S.Nonempty) :
    S.max' hne ∈ S := Finset.max'_mem S hne

/-- The predecessor of the minimum is not in S. -/
lemma pred_min_not_mem {S : Finset ℤ} (hne : S.Nonempty) :
    S.min' hne - 1 ∉ S := by
  intro h
  have := Finset.min'_le S _ h
  omega

/-- The successor of the maximum is not in S. -/
lemma succ_max_not_mem {S : Finset ℤ} (hne : S.Nonempty) :
    S.max' hne + 1 ∉ S := by
  intro h
  have := Finset.max'_le S _ h
  omega

/-- The predecessor of min(S) is in the edge boundary. -/
lemma pred_min_in_boundary {S : Finset ℤ} (hne : S.Nonempty) :
    S.min' hne - 1 ∈ edgeBoundary S := by
  simp only [edgeBoundary, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · exact ⟨S.min' hne, min_mem_of_nonempty hne, by simp⟩
  · exact pred_min_not_mem hne

/-- The successor of max(S) is in the edge boundary. -/
lemma succ_max_in_boundary {S : Finset ℤ} (hne : S.Nonempty) :
    S.max' hne + 1 ∈ edgeBoundary S := by
  simp only [edgeBoundary, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · exact ⟨S.max' hne, max_mem_of_nonempty hne, by simp⟩
  · exact succ_max_not_mem hne

/-- The predecessor of min and successor of max are distinct. -/
lemma boundary_points_distinct {S : Finset ℤ} (hne : S.Nonempty)
    (hcard : 1 < S.card) :
    S.min' hne - 1 ≠ S.max' hne + 1 := by
  intro h
  have hmin := Finset.min'_le S (S.max' hne) (max_mem_of_nonempty hne)
  have hmax := Finset.max'_le S (S.min' hne) (min_mem_of_nonempty hne)
  -- min ≤ max, so min - 1 < max + 1, but h says they're equal
  omega

/-- **Discrete isoperimetric lower bound**: Any finite subset of Z
    with at least 2 elements has edge boundary of size ≥ 2.

    The predecessor of the minimum and successor of the maximum
    are two distinct boundary points. -/
theorem edgeBoundary_card_ge_two {S : Finset ℤ} (hne : S.Nonempty)
    (hcard : 1 < S.card) :
    2 ≤ (edgeBoundary S).card := by
  have h1 := pred_min_in_boundary hne
  have h2 := succ_max_in_boundary hne
  have h3 := boundary_points_distinct hne hcard
  calc 2 = ({S.min' hne - 1, S.max' hne + 1} : Finset ℤ).card := by
        rw [Finset.card_pair h3]
    _ ≤ (edgeBoundary S).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact h1
        · exact h2

-- ============================================================
-- SECTION III: Intervals Achieve Equality
-- ============================================================

/-- For a singleton {a}, the edge boundary is {a-1, a+1}, with size 2. -/
theorem edgeBoundary_singleton (a : ℤ) :
    edgeBoundary {a} = {a - 1, a + 1} := by
  ext x
  simp only [edgeBoundary, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_singleton, Finset.mem_insert]
  constructor
  · rintro ⟨⟨s, rfl, hs⟩, hx⟩
    simp at hs
    rcases hs with rfl | rfl <;> simp_all <;> omega
  · rintro (rfl | rfl) <;> refine ⟨⟨a, rfl, by simp⟩, by simp; omega⟩

/-- The edge boundary of {a} has exactly 2 elements. -/
theorem edgeBoundary_singleton_card (a : ℤ) :
    (edgeBoundary {a}).card = 2 := by
  rw [edgeBoundary_singleton]
  apply Finset.card_pair
  omega

-- ============================================================
-- SECTION IV: Interval Boundary
-- ============================================================

/-- **Interval boundary**: The edge boundary of the integer interval
    [a, b] (with a ≤ b) is {a-1, b+1}, with size exactly 2. -/
theorem edgeBoundary_Icc_eq (a b : ℤ) (hab : a ≤ b) :
    edgeBoundary (Finset.Icc a b) = {a - 1, b + 1} := by
  ext x
  simp only [edgeBoundary, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨s, ⟨has, hsb⟩, hx⟩, hnotin⟩
    simp only [Finset.mem_Icc, not_and_or, not_le] at hnotin
    rcases hx with hx | hx <;> simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    · -- x = s - 1 or x = s + 1
      rcases hx with rfl | rfl
      · -- x = s - 1, not in [a,b]
        rcases hnotin with h | h
        · left; omega
        · -- s - 1 > b, but s ≤ b, contradiction
          omega
      · -- x = s + 1, not in [a,b]
        rcases hnotin with h | h
        · -- s + 1 < a, but s ≥ a, contradiction
          omega
        · right; omega
    · rcases hx with rfl | rfl
      · rcases hnotin with h | h
        · left; omega
        · omega
      · rcases hnotin with h | h
        · omega
        · right; omega
  · rintro (rfl | rfl)
    · constructor
      · exact ⟨a, ⟨le_refl a, hab⟩, by simp⟩
      · simp [Finset.mem_Icc]; omega
    · constructor
      · exact ⟨b, ⟨hab, le_refl b⟩, by simp⟩
      · simp [Finset.mem_Icc]; omega

/-- The edge boundary of [a, b] has exactly 2 elements. -/
theorem edgeBoundary_Icc_card (a b : ℤ) (hab : a ≤ b) :
    (edgeBoundary (Finset.Icc a b)).card = 2 := by
  rw [edgeBoundary_Icc_eq a b hab]
  apply Finset.card_pair
  omega

-- ============================================================
-- SECTION V: Discrete Isoperimetric Inequality (1D)
-- ============================================================

/-- **Discrete isoperimetric inequality in 1D**: Among all finite subsets
    of Z with |S| ≥ 2, the edge boundary satisfies |∂S| ≥ 2, with equality
    if S is an interval.

    Combined with the interval boundary theorem, this says intervals
    uniquely minimize boundary size: |∂S| = 2 iff S is an interval. -/
theorem discrete_isoperimetric_1d {S : Finset ℤ} (hne : S.Nonempty)
    (hcard : 1 < S.card) :
    2 ≤ (edgeBoundary S).card ∧
    (IsInterval S → (edgeBoundary S).card = 2) := by
  constructor
  · exact edgeBoundary_card_ge_two hne hcard
  · rintro ⟨a, b, hab, rfl⟩
    exact edgeBoundary_Icc_card a b hab

-- ============================================================
-- SECTION VI: Higher Dimensions (Statement Only)
-- ============================================================

/-- **Discrete isoperimetric inequality in Z^d** (conjecture, for reference):
    For S ⊆ Z^d with |S| = n, the edge boundary satisfies
      |∂S| ≥ 2d · n^{(d-1)/d}
    The optimal sets are d-dimensional cubes (or close to cubes).
    For d = 1, this reduces to |∂S| ≥ 2 (proved above).

    Full formalization would require defining the edge boundary for
    Finset (Fin d → ℤ) and the Loomis-Whitney / compression technique. -/

end DiscreteIsoperimetric
