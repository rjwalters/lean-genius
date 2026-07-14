/-
  Aristotle targets for Erdős Problem #1043
  Routine supporting lemmas for automated proof search.
  See Erdos1043Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main hard results (disk projection measure, level set compactness)
  - Routine order/lattice facts: iInf ≤ iSup, ENNReal arithmetic contradictions
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings
-/
import Mathlib

open scoped ENNReal

namespace Erdos1043.Aristotle

/-
  ## Section 1: ENNReal Arithmetic

  EHP_conjecture_false closes after establishing:
    hu   : x ≤ 2
    hge  : x ≥ 2.386
  The contradiction follows because 2 < 2.386 in ℝ≥0∞.
-/

-- v4.31: `norm_num` no longer evaluates `ENNReal` scientific-notation literals
-- directly. Bridge to `NNReal` (`(d : ℝ≥0∞) = ((d : NNReal) : ℝ≥0∞)` holds by `rfl`
-- for a scientific literal `d`), then cast to `ℝ` where `norm_num` is complete.
private lemma nnreal_lt_of_scientific {a b : NNReal} (h : (a : ℝ) < b) : a < b := by
  rwa [← NNReal.coe_lt_coe]

private lemma nnreal_le_of_scientific {a b : NNReal} (h : (a : ℝ) ≤ b) : a ≤ b := by
  rwa [← NNReal.coe_le_coe]

-- Aristotle target: 2 < 2.386 in ENNReal
theorem two_lt_two_point_386 : (2 : ℝ≥0∞) < 2.386 := by
  rw [show (2 : ℝ≥0∞) = ((2 : NNReal) : ℝ≥0∞) from by norm_num,
      show (2.386 : ℝ≥0∞) = ((2.386 : NNReal) : ℝ≥0∞) from rfl, ENNReal.coe_lt_coe]
  exact nnreal_lt_of_scientific (by push_cast; norm_num)

-- Aristotle target: contradiction from ≥ 2.386 and ≤ 2 in ENNReal
theorem ennreal_contradiction_2_386 (x : ℝ≥0∞)
    (hge : (2.386 : ℝ≥0∞) ≤ x) (hle : x ≤ 2) : False := by
  have h : (2.386 : ℝ≥0∞) ≤ 2 := le_trans hge hle
  rw [show (2.386 : ℝ≥0∞) = ((2.386 : NNReal) : ℝ≥0∞) from rfl,
      show (2 : ℝ≥0∞) = ((2 : NNReal) : ℝ≥0∞) from by norm_num, ENNReal.coe_le_coe] at h
  exact absurd h (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)

-- Aristotle target: 2 ≤ 3.3 in ENNReal
theorem two_le_3_3 : (2 : ℝ≥0∞) ≤ 3.3 := by
  rw [show (2 : ℝ≥0∞) = ((2 : NNReal) : ℝ≥0∞) from by norm_num,
      show (3.3 : ℝ≥0∞) = ((3.3 : NNReal) : ℝ≥0∞) from rfl, ENNReal.coe_le_coe]
  exact nnreal_le_of_scientific (by push_cast; norm_num)

-- Aristotle target: 2.386 ≤ 3.3 in ENNReal
theorem two_386_le_3_3 : (2.386 : ℝ≥0∞) ≤ 3.3 := by
  rw [show (2.386 : ℝ≥0∞) = ((2.386 : NNReal) : ℝ≥0∞) from rfl,
      show (3.3 : ℝ≥0∞) = ((3.3 : NNReal) : ℝ≥0∞) from rfl, ENNReal.coe_le_coe]
  exact nnreal_le_of_scientific (by push_cast; norm_num)

/-
  ## Section 2: iInf Bounds for min_projection_bounded

  min_projection_bounded states: ⨅ u, projectionMeasure u (unitLevelSet f) ≤ 3.3

  Given pommerenke_upper_bound: ∃ u, projectionMeasure u (unitLevelSet f) ≤ 3.3
  we need: iInf ≤ that particular value.
-/

-- Aristotle target: iInf over a type ≤ any particular value
-- (same as iInf_le, but explicit)
theorem iInf_le_of_witness {α : Type*} [Nonempty α] (f : α → ℝ≥0∞)
    (u : α) (b : ℝ≥0∞) (hu : f u ≤ b) : iInf f ≤ b :=
  le_trans (iInf_le f u) hu

/-
  ## Section 3: minWidth ≤ maxWidth

  convex_width_bounds needs: minWidth S ≤ maxWidth S
  where minWidth = ⨅ u, width S u and maxWidth = ⨆ u, width S u.
  This holds because iInf ≤ iSup for the same nonempty index type.
-/

-- Aristotle target: iInf ≤ iSup over same nonempty index type
theorem iInf_le_iSup {α : Type*} [Nonempty α] (f : α → ℝ≥0∞) :
    iInf f ≤ iSup f :=
  let ⟨a⟩ := ‹Nonempty α›
  le_trans (iInf_le f a) (le_iSup f a)

/-
  ## Section 4: Measure Positivity

  Supporting arithmetic facts.
-/

-- Aristotle target: projection measure bound 0 < 2
theorem zero_lt_two_ennreal : (0 : ℝ≥0∞) < 2 := by norm_num

-- Aristotle target: projection measure bound 0 < 3.3
theorem zero_lt_3_3_ennreal : (0 : ℝ≥0∞) < 3.3 := by
  rw [show (0 : ℝ≥0∞) = ((0 : NNReal) : ℝ≥0∞) from by norm_num,
      show (3.3 : ℝ≥0∞) = ((3.3 : NNReal) : ℝ≥0∞) from rfl, ENNReal.coe_lt_coe]
  exact nnreal_lt_of_scientific (by push_cast; norm_num)

-- Aristotle target: 0 < 2.386 in ENNReal
theorem zero_lt_2_386_ennreal : (0 : ℝ≥0∞) < 2.386 := by
  rw [show (0 : ℝ≥0∞) = ((0 : NNReal) : ℝ≥0∞) from by norm_num,
      show (2.386 : ℝ≥0∞) = ((2.386 : NNReal) : ℝ≥0∞) from rfl, ENNReal.coe_lt_coe]
  exact nnreal_lt_of_scientific (by push_cast; norm_num)

end Erdos1043.Aristotle
