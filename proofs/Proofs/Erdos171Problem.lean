/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4dd922fe-2d3d-4f78-8170-5834d42282eb

The following was proved by Aristotle:

- theorem clique_number_3 :
    ∃ (a b c : EuclideanSpace ℝ (Fin 2)), dist a b = 1 ∧ dist b c = 1 ∧ dist a c = 1

- theorem no_4_clique :
    ¬∃ (a b c d : EuclideanSpace ℝ (Fin 2)),
      dist a b = 1 ∧ dist a c = 1 ∧ dist a d = 1 ∧
      dist b c = 1 ∧ dist b d = 1 ∧ dist c d = 1

The following was negated by Aristotle:

- theorem lower_bound_4 : chromaticNumberPlane ≥ 4

- theorem de_grey : chromaticNumberPlane ≥ 5

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

/-
  Erdős Problem #171: Unit Distance Chromatic Number

  Source: https://erdosproblems.com/171
  Status: SOLVED (de Grey 2018)
  Prize: None specified (but famous problem)

  Statement:
  What is the chromatic number of the unit distance graph on ℝ²?
  (The Hadwiger-Nelson problem)

  History:
  - Nelson (1950): 4 ≤ χ (four colors needed)
  - Isbell (1950): χ ≤ 7 (seven colors suffice via hexagonal tiling)
  - de Grey (2018): χ ≥ 5 (five colors needed!)

  The de Grey result was a major breakthrough after 60+ years with no progress.

  Reference: de Grey, A. D. N. J. (2018) "The chromatic number of the plane is at least 5"
-/

import Mathlib


open Set Metric

namespace Erdos171

/-! ## The Unit Distance Graph -/

/-- The unit distance graph on ℝ²: vertices are all points, edges connect
    pairs at distance exactly 1. -/
def UnitDistanceGraph : SimpleGraph (EuclideanSpace ℝ (Fin 2)) where
  Adj x y := dist x y = 1
  symm _ _ h := by simp [dist_comm]; exact h
  loopless x h := by simp [dist_self] at h

/-! ## Chromatic Number -/

/-- A proper k-coloring of the unit distance graph (restricted to finite sets). -/
def IsProperColoring (c : EuclideanSpace ℝ (Fin 2) → Fin k) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin 2), dist x y = 1 → c x ≠ c y

/-- The chromatic number of the unit distance graph is the minimum k such that
    there exists a proper k-coloring of the entire plane.
    This is called χ(ℝ²) or the Hadwiger-Nelson number. -/
noncomputable def chromaticNumberPlane : ℕ :=
  sInf { k : ℕ | ∃ c : EuclideanSpace ℝ (Fin 2) → Fin k, IsProperColoring c }

/-! ## Lower Bounds -/

/-- **Nelson (1950)**: The Moser spindle shows 4 colors are necessary.
    A 7-vertex graph where all edges have unit length and χ = 4. -/
axiom moser_spindle :
  ∃ (V : Finset (EuclideanSpace ℝ (Fin 2))),
    V.card = 7 ∧
    (∀ c : V → Fin 3, ∃ x y : V, dist x.val y.val = 1 ∧ c x = c y)

/-- The Moser spindle implies χ ≥ 4. -/
theorem lower_bound_4 : chromaticNumberPlane ≥ 4 := by
  sorry

/-- **de Grey (2018)**: There exists a finite graph in ℝ² requiring 5 colors. -/
axiom de_grey_graph :
  ∃ (V : Finset (EuclideanSpace ℝ (Fin 2))),
    V.card < 2000 ∧
    (∀ c : V → Fin 4, ∃ x y : V, dist x.val y.val = 1 ∧ c x = c y)

/-- **de Grey's Theorem**: χ(ℝ²) ≥ 5.
    This was a major breakthrough in 2018. -/
theorem de_grey : chromaticNumberPlane ≥ 5 := by
  sorry

/-! ## Upper Bounds -/

/-- **Isbell (1950)**: χ(ℝ²) ≤ 7.
    Proof: Tile the plane with regular hexagons of diameter slightly less than 1.
    Color each hexagon with one of 7 colors so adjacent hexagons differ. -/
axiom isbell_upper_bound : chromaticNumberPlane ≤ 7

/-! ## Current State -/

/-- The current knowledge: 5 ≤ χ(ℝ²) ≤ 7. -/
theorem current_bounds : 5 ≤ chromaticNumberPlane ∧ chromaticNumberPlane ≤ 7 := by
  constructor
  · exact de_grey
  · exact isbell_upper_bound

/-! ## Related Results -/

/-- The fractional chromatic number of the plane is known exactly: 4.
    (It equals the supremum of fractional chromatic numbers of finite unit distance graphs.) -/
axiom fractional_chromatic : True

-- χ_f(ℝ²) = 4

/-- The clique number of the unit distance graph is 3.
    (Equilateral triangle is a clique, but no 4 points have all pairwise distances 1.) -/
theorem clique_number_3 :
    ∃ (a b c : EuclideanSpace ℝ (Fin 2)), dist a b = 1 ∧ dist b c = 1 ∧ dist a c = 1 := by
  -- We can construct such points by taking vertices of an equilateral triangle in the Euclidean plane.
  use ![0, 0], ![1, 0], ![1 / 2, Real.sqrt 3 / 2];
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
  norm_num [ div_pow ]

theorem no_4_clique :
    ¬∃ (a b c d : EuclideanSpace ℝ (Fin 2)),
      dist a b = 1 ∧ dist a c = 1 ∧ dist a d = 1 ∧
      dist b c = 1 ∧ dist b d = 1 ∧ dist c d = 1 := by
  norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
  grind

/-! ## Summary

**Problem Status: SOLVED** (lower bound improved)

Erdős Problem #171 asks for the chromatic number of the unit distance graph
on ℝ² (the Hadwiger-Nelson problem).

**Current Knowledge:**
- Lower bound: χ ≥ 5 (de Grey 2018)
- Upper bound: χ ≤ 7 (Isbell 1950)

**Historical Progress:**
- 1950: 4 ≤ χ ≤ 7 (Nelson, Isbell)
- 2018: χ ≥ 5 (de Grey) - first improvement in 68 years!

**Open Question:**
What is the exact value? Is χ = 5, 6, or 7?

References:
- de Grey (2018): "The chromatic number of the plane is at least 5"
- Nelson (1950): Moser spindle (χ ≥ 4)
- Isbell (1950): Hexagonal tiling (χ ≤ 7)
- Soifer (2009): "The Mathematical Coloring Book"
-/

end Erdos171