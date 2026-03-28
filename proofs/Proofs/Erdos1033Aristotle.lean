/-
  Aristotle targets for Erdős Problem #1033
  Routine supporting lemmas for automated proof search.
  See Erdos1033Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture or deep extremal results
  - Known results provable from definitions or basic Mathlib facts
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos1033Aristotle

open Finset Real

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The constant 2(√3 - 1). -/
noncomputable def erdosLaskarConstant : ℝ := 2 * (Real.sqrt 3 - 1)

/-- Fan's constant 21/16 = 1.3125. -/
def fanConstant : ℚ := 21 / 16

/-- The gap between bounds. -/
noncomputable def boundGap : ℝ := erdosLaskarConstant - fanConstant

/-- A triangle in G: three mutually adjacent vertices. -/
structure Triangle (G : SimpleGraph V) where
  v1 : V
  v2 : V
  v3 : V
  distinct12 : v1 ≠ v2
  distinct23 : v2 ≠ v3
  distinct13 : v1 ≠ v3
  adj12 : G.Adj v1 v2
  adj23 : G.Adj v2 v3
  adj13 : G.Adj v1 v3

/-- Degree of a vertex in a decidable graph. -/
noncomputable def vertexDegree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  G.degree v

/-- Sum of degrees of the three vertices in a triangle. -/
noncomputable def triangleDegreeSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) : ℕ :=
  vertexDegree G T.v1 + vertexDegree G T.v2 + vertexDegree G T.v3

-- Helper: if a 2-element subset of neighbors exists, degree ≥ 2
private theorem degree_ge_two_of_adj_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (v a b : V) (hab : a ≠ b) (ha : G.Adj v a) (hb : G.Adj v b) :
    G.degree v ≥ 2 := by
  have ha' : a ∈ G.neighborFinset v := SimpleGraph.mem_neighborFinset.mpr ha
  have hb' : b ∈ G.neighborFinset v := SimpleGraph.mem_neighborFinset.mpr hb
  have hsub : ({a, b} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
  calc G.degree v = (G.neighborFinset v).card := rfl
    _ ≥ ({a, b} : Finset V).card := Finset.card_le_card hsub
    _ = 2 := Finset.card_pair hab

-- Routine: Each vertex in a triangle has degree ≥ 2
theorem triangle_min_degree (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) :
    vertexDegree G T.v1 ≥ 2 ∧ vertexDegree G T.v2 ≥ 2 ∧ vertexDegree G T.v3 ≥ 2 := by
  unfold vertexDegree
  exact ⟨degree_ge_two_of_adj_pair G T.v1 T.v2 T.v3 T.distinct23 T.adj12 T.adj13,
         degree_ge_two_of_adj_pair G T.v2 T.v1 T.v3 T.distinct13 (G.symm T.adj12) T.adj23,
         degree_ge_two_of_adj_pair G T.v3 T.v1 T.v2 T.distinct12 (G.symm T.adj13) (G.symm T.adj23)⟩

-- Routine: Triangle degree sum is at least 6 (each vertex has degree ≥ 2)
theorem triangle_sum_min (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) :
    triangleDegreeSum G T ≥ 6 := by
  unfold triangleDegreeSum
  have ⟨h1, h2, h3⟩ := triangle_min_degree G T
  omega

-- Routine: Numerical estimate 2(√3-1) > 1.46
-- Proof: 2(√3-1) > 1.46 ⟺ √3 > 1.73 ⟺ 3 > 1.73² = 2.9929
theorem erdosLaskar_gt : erdosLaskarConstant > 1.46 := by
  unfold erdosLaskarConstant
  have h : (1.73 : ℝ) < Real.sqrt 3 := by
    rw [show (1.73 : ℝ) = Real.sqrt (1.73 ^ 2) from
      (Real.sqrt_sq (by norm_num : (1.73 : ℝ) ≥ 0)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

-- Routine: Numerical estimate 2(√3-1) < 1.47
-- Proof: 2(√3-1) < 1.47 ⟺ √3 < 1.735 ⟺ 3 < 1.735² = 3.010225
theorem erdosLaskar_lt : erdosLaskarConstant < 1.47 := by
  unfold erdosLaskarConstant
  have h : Real.sqrt 3 < 1.735 := by
    rw [show (1.735 : ℝ) = Real.sqrt (1.735 ^ 2) from
      (Real.sqrt_sq (by norm_num : (1.735 : ℝ) ≥ 0)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

-- Routine: Fan's constant is greater than 1
theorem fan_gt_one : (fanConstant : ℝ) > 1 := by
  simp only [fanConstant]; norm_num

-- Routine: Fan's constant equals 1.3125
theorem fan_value : (fanConstant : ℝ) = 21 / 16 := by
  simp only [fanConstant]; norm_num

-- Routine: The gap between bounds is positive
-- 2(√3-1) ≈ 1.464 > 1.3125 = 21/16
theorem gap_positive : boundGap > 0 := by
  unfold boundGap
  have h := erdosLaskar_gt  -- 2(√3-1) > 1.46
  have hf := fan_value       -- fanConstant = 21/16 = 1.3125
  linarith

-- Routine: erdosLaskarConstant > fanConstant
theorem erdosLaskar_gt_fan : erdosLaskarConstant > (fanConstant : ℝ) := by
  have h := erdosLaskar_gt  -- > 1.46
  have hf := fan_value       -- = 1.3125
  linarith

-- Routine: 2(√3-1) > 0
theorem erdosLaskar_pos : erdosLaskarConstant > 0 := by
  unfold erdosLaskarConstant
  have h1 : Real.sqrt 3 > 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end Erdos1033Aristotle
