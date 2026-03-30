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

/- ## The Unit Distance Graph -/

/-- The unit distance graph on ℝ²: vertices are all points, edges connect
    pairs at distance exactly 1. -/
def UnitDistanceGraph : SimpleGraph (EuclideanSpace ℝ (Fin 2)) where
  Adj x y := dist x y = 1
  symm _ _ h := by simp [dist_comm]; exact h
  loopless x h := by simp [dist_self] at h

/- ## Chromatic Number -/

/-- A proper k-coloring of the unit distance graph (restricted to finite sets). -/
def IsProperColoring (c : EuclideanSpace ℝ (Fin 2) → Fin k) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin 2), dist x y = 1 → c x ≠ c y

/-- The chromatic number of the unit distance graph is the minimum k such that
    there exists a proper k-coloring of the entire plane.
    This is called χ(ℝ²) or the Hadwiger-Nelson number. -/
noncomputable def chromaticNumberPlane : ℕ :=
  sInf { k : ℕ | ∃ c : EuclideanSpace ℝ (Fin 2) → Fin k, IsProperColoring c }

/- ## Upper Bounds -/

/-- A proper 7-coloring of the plane exists (Isbell 1950, hexagonal tiling).
    This witnesses the colorability set as nonempty, enabling lower bound proofs. -/
axiom isbell_coloring :
  ∃ c : EuclideanSpace ℝ (Fin 2) → Fin 7, IsProperColoring c

/-- **Isbell (1950)**: χ(ℝ²) ≤ 7.
    Proof: Tile the plane with regular hexagons of diameter slightly less than 1.
    Color each hexagon with one of 7 colors so adjacent hexagons differ. -/
theorem isbell_upper_bound : chromaticNumberPlane ≤ 7 := by
  unfold chromaticNumberPlane
  exact Nat.sInf_le isbell_coloring

/- ## Lower Bounds -/

/-! ### Moser Spindle: Explicit Construction

We construct the 7 vertices of the Moser spindle in ℝ² using Warren D. Smith's
coordinates from the complex formulation z ∈ {0, 1, 1+ω, 2+ω, a, a+aω, 2a+aω}
where ω = e^{2πi/3} and a = e^{i·arccos(5/6)}. All coordinates lie in Q(√3, √11).
The 11 edges all have unit distance, and the graph requires 4 colors. -/

/-- Adjacency of the Moser spindle graph on Fin 7.
    Edges: 0-1, 0-2, 0-4, 0-5, 1-2, 1-3, 2-3, 3-6, 4-5, 4-6, 5-6 -/
private def moserAdj (i j : Fin 7) : Bool :=
  let a := min i.val j.val
  let b := max i.val j.val
  (a == 0 && b == 1) || (a == 0 && b == 2) || (a == 0 && b == 4) || (a == 0 && b == 5) ||
  (a == 1 && b == 2) || (a == 1 && b == 3) || (a == 2 && b == 3) || (a == 3 && b == 6) ||
  (a == 4 && b == 5) || (a == 4 && b == 6) || (a == 5 && b == 6)

/-- The Moser spindle is not 3-colorable: every 3-coloring has a monochromatic edge. -/
private theorem moser_not_3_colorable :
    ∀ c : Fin 7 → Fin 3, ∃ i j : Fin 7, moserAdj i j = true ∧ c i = c j := by
  native_decide

/-- The 7 vertices of the Moser spindle in ℝ². -/
private noncomputable def moserPt : Fin 7 → EuclideanSpace ℝ (Fin 2)
  | 0 => ![0, 0]
  | 1 => ![1, 0]
  | 2 => ![1/2, Real.sqrt 3 / 2]
  | 3 => ![3/2, Real.sqrt 3 / 2]
  | 4 => ![5/6, Real.sqrt 11 / 6]
  | 5 => ![(5 - Real.sqrt 3 * Real.sqrt 11) / 12,
           (5 * Real.sqrt 3 + Real.sqrt 11) / 12]
  | 6 => ![(15 - Real.sqrt 3 * Real.sqrt 11) / 12,
           (5 * Real.sqrt 3 + 3 * Real.sqrt 11) / 12]

private theorem sqrt3_sq' : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private theorem sqrt11_sq' : (Real.sqrt 11) ^ 2 = 11 := Real.sq_sqrt (by norm_num)

private theorem sqrt33_sq' : (Real.sqrt 3 * Real.sqrt 11) ^ 2 = 33 := by
  rw [mul_pow, sqrt3_sq', sqrt11_sq']; norm_num

/-- (5 - √33)/12 ≠ r when (5 - 12r)² ≠ 33. Used for injectivity. -/
private theorem moser_x5_ne (r : ℝ) (hr : (5 - 12 * r) ^ 2 ≠ 33) :
    (5 - Real.sqrt 3 * Real.sqrt 11) / 12 ≠ r := by
  intro h; apply hr
  have : Real.sqrt 3 * Real.sqrt 11 = 5 - 12 * r := by linarith
  rw [← this]; exact sqrt33_sq'

/-- (15 - √33)/12 ≠ r when (15 - 12r)² ≠ 33. Used for injectivity. -/
private theorem moser_x6_ne (r : ℝ) (hr : (15 - 12 * r) ^ 2 ≠ 33) :
    (15 - Real.sqrt 3 * Real.sqrt 11) / 12 ≠ r := by
  intro h; apply hr
  have : Real.sqrt 3 * Real.sqrt 11 = 15 - 12 * r := by linarith
  rw [← this]; exact sqrt33_sq'

/-- All 7 Moser spindle points are distinct (proved via x-coordinate comparison). -/
private theorem moserPt_injective : Function.Injective moserPt := by
  intro i j h
  have h0 := congr_arg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h
  fin_cases i <;> fin_cases j <;>
    simp only [moserPt, Matrix.cons_val_zero, Matrix.head_cons] at h0 ⊢ <;>
    first
    | rfl
    | (exfalso; norm_num at h0)
    | (exfalso; exact moser_x5_ne _ (by norm_num) h0)
    | (exfalso; exact moser_x5_ne _ (by norm_num) h0.symm)
    | (exfalso; exact moser_x6_ne _ (by norm_num) h0)
    | (exfalso; exact moser_x6_ne _ (by norm_num) h0.symm)
    | (exfalso; field_simp at h0; linarith)

/-- Sum of squared coordinate differences = 1 for each Moser spindle edge. -/
private theorem moser_coord_sq (i j : Fin 7) (h : moserAdj i j = true) :
    (moserPt i 0 - moserPt j 0) ^ 2 + (moserPt i 1 - moserPt j 1) ^ 2 = 1 := by
  fin_cases i <;> fin_cases j <;> simp_all [moserAdj] <;>
    simp only [moserPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    ring_nf <;> nlinarith [sqrt3_sq', sqrt11_sq']

/-- Each edge of the Moser spindle has unit Euclidean distance. -/
private theorem moser_edges_unit (i j : Fin 7) (h : moserAdj i j = true) :
    dist (moserPt i) (moserPt j) = 1 := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, Pi.sub_apply, Real.norm_eq_abs, sq_abs]
  rw [moser_coord_sq i j h, Real.sqrt_one]

/-- **Nelson (1950)**: The Moser spindle shows 4 colors are necessary.
    A 7-vertex graph where all edges have unit length and χ = 4.
    PROVED: explicit construction with coordinates in Q(√3, √11). -/
theorem moser_spindle :
    ∃ (V : Finset (EuclideanSpace ℝ (Fin 2))),
      V.card = 7 ∧
      (∀ c : V → Fin 3, ∃ x y : V, dist x.val y.val = 1 ∧ c x = c y) := by
  refine ⟨Finset.image moserPt Finset.univ, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ moserPt_injective, Finset.card_fin]
  · intro c
    obtain ⟨i, j, hadj, hcolor⟩ := moser_not_3_colorable
      (fun k => c ⟨moserPt k, Finset.mem_image_of_mem _ (Finset.mem_univ k)⟩)
    exact ⟨⟨moserPt i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩,
           ⟨moserPt j, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩,
           moser_edges_unit i j hadj, hcolor⟩

/-- The Moser spindle implies χ ≥ 4: any proper k-coloring of the plane restricts
    to a proper coloring of the Moser spindle vertices, but 3 colors don't suffice. -/
theorem lower_bound_4 : chromaticNumberPlane ≥ 4 := by
  unfold chromaticNumberPlane
  apply le_csInf ⟨7, isbell_coloring⟩
  intro k ⟨c, hc⟩
  by_contra hlt
  push_neg at hlt
  have hle : k ≤ 3 := by omega
  obtain ⟨V, -, hno⟩ := moser_spindle
  obtain ⟨x, y, hdist, heq⟩ :=
    hno (fun v => ⟨(c v.val).val, lt_of_lt_of_le (c v.val).isLt hle⟩)
  exact absurd (Fin.ext (congr_arg Fin.val heq)) (hc x.val y.val hdist)

/-- **de Grey (2018)**: There exists a finite graph in ℝ² requiring 5 colors. -/
axiom de_grey_graph :
  ∃ (V : Finset (EuclideanSpace ℝ (Fin 2))),
    V.card < 2000 ∧
    (∀ c : V → Fin 4, ∃ x y : V, dist x.val y.val = 1 ∧ c x = c y)

/-- **de Grey's Theorem**: χ(ℝ²) ≥ 5. Proved from axiom that 4 colors don't suffice
    on a finite subgraph discovered by de Grey in 2018. -/
theorem de_grey : chromaticNumberPlane ≥ 5 := by
  unfold chromaticNumberPlane
  apply le_csInf ⟨7, isbell_coloring⟩
  intro k ⟨c, hc⟩
  by_contra hlt
  push_neg at hlt
  have hle : k ≤ 4 := by omega
  obtain ⟨V, -, hno⟩ := de_grey_graph
  obtain ⟨x, y, hdist, heq⟩ :=
    hno (fun v => ⟨(c v.val).val, lt_of_lt_of_le (c v.val).isLt hle⟩)
  exact absurd (Fin.ext (congr_arg Fin.val heq)) (hc x.val y.val hdist)

/- ## Current State -/

/-- The current knowledge: 5 ≤ χ(ℝ²) ≤ 7. -/
theorem current_bounds : 5 ≤ chromaticNumberPlane ∧ chromaticNumberPlane ≤ 7 := by
  constructor
  · exact de_grey
  · exact isbell_upper_bound

/- ## Related Results -/

/- The fractional chromatic number of the plane is known exactly: 4.
    (It equals the supremum of fractional chromatic numbers of finite unit distance graphs.) -/

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

/- ## Summary

**Problem Status: SOLVED** (lower bound improved)

Erdős Problem #171 asks for the chromatic number of the unit distance graph
on ℝ² (the Hadwiger-Nelson problem).

**Current Knowledge:**
- Lower bound: χ ≥ 5 (de Grey 2018)
- Upper bound: χ ≤ 7 (Isbell 1950)

**Proved (7+ theorems):**
- moser_spindle: Explicit Moser spindle in Q(√3, √11) with native_decide
- lower_bound_4, de_grey, current_bounds, isbell_upper_bound
- clique_number_3, no_4_clique (Aristotle-verified)

**Axiomatized (2 axioms):**
- isbell_coloring: A proper 7-coloring of ℝ² exists (hexagonal tiling)
- de_grey_graph: A finite ℝ² graph requiring 5 colors (1581 vertices)

References:
- de Grey (2018): "The chromatic number of the plane is at least 5"
- Nelson (1950): Moser spindle (χ ≥ 4)
- Isbell (1950): Hexagonal tiling (χ ≤ 7)
- Soifer (2009): "The Mathematical Coloring Book"
-/

end Erdos171