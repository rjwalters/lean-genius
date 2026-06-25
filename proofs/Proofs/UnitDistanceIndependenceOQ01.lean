/-
# A Machine-Checked Lower Bound χ(ℝ²) ≥ 4 via the Moser Spindle

Open question OQ-01 of `unit-distance-independence`.

The parent formalization (`UnitDistanceIndependence.lean`) records the
Hadwiger–Nelson bounds `5 ≤ χ(ℝ²) ≤ 7`: the upper bound `≤ 7` is a fully
machine-checked theorem (hexagonal 7-colouring, `UnitDistanceHN7.lean`), while
the lower bound `χ(ℝ²) ≥ 5` is **axiomatized** (de Grey 2018 — a genuinely hard
1581-vertex construction).

This file supplies the *strongest unconditional, fully verified* lower bound the
gallery was missing: a 0-axiom proof that

    χ(ℝ²) ≥ 4,

i.e. **no 3-colouring of the plane avoids monochromatic unit-distance pairs**.
This is the classical Moser–Moser (1961) bound, obtained by exhibiting the
**Moser spindle**: a 7-vertex, 11-edge unit-distance graph whose chromatic
number is 4.

**Strategy** (entirely elementary, no `native_decide`):

1. *Combinatorics.* The abstract spindle graph on `Fin 7` is not properly
   3-colourable: for every `f : Fin 7 → Fin 3` two adjacent vertices share a
   colour. This is a finite check (`decide`, 3⁷ = 2187 colourings).

2. *Geometry.* The 7 vertices are realized in ℝ² so that every spindle edge has
   Euclidean length exactly 1. The construction is two rhombi (each a pair of
   unit equilateral triangles) sharing a vertex at the origin, the second
   rhombus being the first rotated by the angle `θ` with `cos θ = 5/6`,
   `sin θ = √11/6` — the unique rotation bringing the two far tips to unit
   distance. The irrationality `√11` is intrinsic to the spindle.

3. *Bridge.* Any unit-distance-avoiding colouring of the plane, restricted to
   the 7 vertices, would be a proper 3-colouring of the spindle — impossible.

Together with the parent's verified `χ(ℝ²) ≤ 7`, this gives the fully
machine-checked window `4 ≤ χ(ℝ²) ≤ 7`, with the sharper `≥ 5` remaining the one
axiomatized (de Grey) input.

**Status**: VERIFIED (0 sorries, 0 axioms).
Tags: combinatorial-geometry, unit-distance-graphs, hadwiger-nelson, moser-spindle
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace UnitDistanceIndependenceOQ01

open Finset

/-- The plane as the 2-dimensional Euclidean space. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable section

/-- `√3`, the height parameter of the unit equilateral triangle. -/
def s3 : ℝ := Real.sqrt 3

/-- `√11`; `√11 / 6 = sin θ` for the spindle's rotation angle. -/
def s11 : ℝ := Real.sqrt 11

/-- Construct a plane point from its two Cartesian coordinates. -/
def mk (x y : ℝ) : Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x, y]

/-- The rotation by the spindle angle `θ` (`cos θ = 5/6`, `sin θ = √11/6`)
    about the origin. -/
def rot (p : Plane) : Plane :=
  mk (5 / 6 * p 0 - s11 / 6 * p 1) (s11 / 6 * p 0 + 5 / 6 * p 1)

/-- Reading back the first coordinate of `mk x y`. -/
theorem mk_zero (x y : ℝ) : (mk x y) 0 = x := by
  simp only [mk, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply,
             Matrix.cons_val_zero]

/-- Reading back the second coordinate of `mk x y`. -/
theorem mk_one (x y : ℝ) : (mk x y) 1 = y := by
  simp only [mk, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply,
             Matrix.cons_val_one, Matrix.cons_val_zero]

/-- Squared distance between two explicit points is the sum of squared
    coordinate differences. -/
theorem dist_mk_sq (x₁ y₁ x₂ y₂ : ℝ) :
    dist (mk x₁ y₁) (mk x₂ y₂) ^ 2 = (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [mk, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply,
             Matrix.cons_val_zero, Matrix.cons_val_one,
             Real.dist_eq, sq_abs]

/-- From a squared-distance computation equal to `1`, conclude the distance is
    `1` (using `dist ≥ 0`). -/
theorem dist_eq_one_of (x₁ y₁ x₂ y₂ : ℝ)
    (h : (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 = 1) :
    dist (mk x₁ y₁) (mk x₂ y₂) = 1 := by
  have hsq : dist (mk x₁ y₁) (mk x₂ y₂) ^ 2 = 1 := by rw [dist_mk_sq]; exact h
  have hnn : (0 : ℝ) ≤ dist (mk x₁ y₁) (mk x₂ y₂) := dist_nonneg
  have hfac :
      (dist (mk x₁ y₁) (mk x₂ y₂) - 1) * (dist (mk x₁ y₁) (mk x₂ y₂) + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h₁ | h₁
  · linarith
  · linarith

/-- `rot` evaluated on an explicit point. -/
theorem rot_mk (a b : ℝ) :
    rot (mk a b) = mk (5 / 6 * a - s11 / 6 * b) (s11 / 6 * a + 5 / 6 * b) := by
  simp only [rot, mk_zero, mk_one]

/-- The origin is fixed by the rotation. -/
theorem rot_origin : rot (mk 0 0) = mk 0 0 := by
  rw [rot_mk]; norm_num

/-- `rot` is an isometry: it preserves Euclidean distance. -/
theorem rot_isometry (p q : Plane) : dist (rot p) (rot q) = dist p q := by
  have hs11 : s11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have hpq : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
    simp only [Real.dist_eq, sq_abs]
  have hrot : dist (rot p) (rot q) ^ 2 =
      (5 / 6 * p 0 - s11 / 6 * p 1 - (5 / 6 * q 0 - s11 / 6 * q 1)) ^ 2 +
      (s11 / 6 * p 0 + 5 / 6 * p 1 - (s11 / 6 * q 0 + 5 / 6 * q 1)) ^ 2 := by
    simp only [rot]; rw [dist_mk_sq]
  have hsq : dist (rot p) (rot q) ^ 2 = dist p q ^ 2 := by
    rw [hrot, hpq]
    linear_combination
      (((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) / 36) * hs11
  have h₁ : (0 : ℝ) ≤ dist (rot p) (rot q) := dist_nonneg
  have h₂ : (0 : ℝ) ≤ dist p q := dist_nonneg
  nlinarith [hsq, h₁, h₂]

/-! ## The seven vertices of the Moser spindle -/

/-- The seven spindle vertices.

* `0`–`3`: the first rhombus (origin, two unit triangles).
* `4`–`6`: the second rhombus, the rotation of vertices `1`–`3` by `θ`. -/
def pt : Fin 7 → Plane
  | 0 => mk 0 0
  | 1 => mk 1 0
  | 2 => mk (1 / 2) (s3 / 2)
  | 3 => mk (3 / 2) (s3 / 2)
  | 4 => rot (mk 1 0)
  | 5 => rot (mk (1 / 2) (s3 / 2))
  | 6 => rot (mk (3 / 2) (s3 / 2))

/-! ### The eleven edges have unit length

First-rhombus edges (only `√3` enters). -/

theorem dist01 : dist (pt 0) (pt 1) = 1 := by
  apply dist_eq_one_of; norm_num

theorem dist02 : dist (pt 0) (pt 2) = 1 := by
  apply dist_eq_one_of
  have hs3 : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination (1 / 4 : ℝ) * hs3

theorem dist12 : dist (pt 1) (pt 2) = 1 := by
  apply dist_eq_one_of
  have hs3 : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination (1 / 4 : ℝ) * hs3

theorem dist13 : dist (pt 1) (pt 3) = 1 := by
  apply dist_eq_one_of
  have hs3 : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination (1 / 4 : ℝ) * hs3

theorem dist23 : dist (pt 2) (pt 3) = 1 := by
  apply dist_eq_one_of; ring

/-! Second-rhombus edges, via the isometry `rot` and the fixed origin. -/

theorem dist04 : dist (pt 0) (pt 4) = 1 := by
  show dist (mk 0 0) (rot (mk 1 0)) = 1
  rw [← rot_origin, rot_isometry]; exact dist01

theorem dist05 : dist (pt 0) (pt 5) = 1 := by
  show dist (mk 0 0) (rot (mk (1 / 2) (s3 / 2))) = 1
  rw [← rot_origin, rot_isometry]; exact dist02

theorem dist45 : dist (pt 4) (pt 5) = 1 := by
  show dist (rot (mk 1 0)) (rot (mk (1 / 2) (s3 / 2))) = 1
  rw [rot_isometry]; exact dist12

theorem dist46 : dist (pt 4) (pt 6) = 1 := by
  show dist (rot (mk 1 0)) (rot (mk (3 / 2) (s3 / 2))) = 1
  rw [rot_isometry]; exact dist13

theorem dist56 : dist (pt 5) (pt 6) = 1 := by
  show dist (rot (mk (1 / 2) (s3 / 2))) (rot (mk (3 / 2) (s3 / 2))) = 1
  rw [rot_isometry]; exact dist23

/-! The bridging edge between the two far tips `D` and `D'` — the unit distance
the rotation angle was chosen to produce. This is the one computation that uses
both `√3` and `√11` (the `√33` cross term cancels). -/

theorem dist36 : dist (pt 3) (pt 6) = 1 := by
  show dist (mk (3 / 2) (s3 / 2)) (rot (mk (3 / 2) (s3 / 2))) = 1
  rw [rot_mk]
  apply dist_eq_one_of
  have hs3 : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs11 : s11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  linear_combination ((s11 ^ 2 + 1) / 144) * hs3 + (12 / 144 : ℝ) * hs11

/-! ### The abstract spindle graph and its chromatic obstruction -/

/-- The 11 edges of the Moser spindle (canonical orientation `i < j`). -/
def isEdge : Fin 7 → Fin 7 → Bool
  | 0, 1 => true
  | 0, 2 => true
  | 1, 2 => true
  | 1, 3 => true
  | 2, 3 => true
  | 0, 4 => true
  | 0, 5 => true
  | 4, 5 => true
  | 4, 6 => true
  | 5, 6 => true
  | 3, 6 => true
  | _, _ => false

/-- In `Fin 3` (three colours), a vertex's colour is determined by the two
    colours it must avoid: if `c` and `d` both differ from the two distinct
    colours `a, b`, then `c = d`. The combinatorial heart of the rhombus
    argument. A 3⁴ = 81-case finite check. -/
theorem fin3_third (a b c d : Fin 3) :
    a ≠ b → c ≠ a → c ≠ b → d ≠ a → d ≠ b → c = d := by
  revert a b c d; decide

/-- **The Moser spindle is not 3-colourable.** For every assignment of 3 colours
    to its 7 vertices, some edge is monochromatic.

    Proof (no brute force over 3⁷ colourings): each rhombus forces its two far
    tips to share a colour. In rhombus `{0,1,2,3}` the triangles `012` and `123`
    use all three colours, so vertices `0` and `3` (each the unique colour
    avoided by `1,2`) satisfy `f 0 = f 3`; likewise `f 0 = f 6` in rhombus
    `{0,4,5,6}`. Hence `f 3 = f 6`, but `3—6` is an edge. -/
theorem spindle_not_3colorable (f : Fin 7 → Fin 3) :
    ∃ i j, isEdge i j = true ∧ f i = f j := by
  by_contra hcon
  push_neg at hcon
  -- All eleven edges are assumed bichromatic.
  have e01 : f 0 ≠ f 1 := hcon 0 1 (by decide)
  have e02 : f 0 ≠ f 2 := hcon 0 2 (by decide)
  have e12 : f 1 ≠ f 2 := hcon 1 2 (by decide)
  have e13 : f 1 ≠ f 3 := hcon 1 3 (by decide)
  have e23 : f 2 ≠ f 3 := hcon 2 3 (by decide)
  have e04 : f 0 ≠ f 4 := hcon 0 4 (by decide)
  have e05 : f 0 ≠ f 5 := hcon 0 5 (by decide)
  have e45 : f 4 ≠ f 5 := hcon 4 5 (by decide)
  have e46 : f 4 ≠ f 6 := hcon 4 6 (by decide)
  have e56 : f 5 ≠ f 6 := hcon 5 6 (by decide)
  have e36 : f 3 ≠ f 6 := hcon 3 6 (by decide)
  -- Far tips of each rhombus share a colour.
  have c03 : f 0 = f 3 := fin3_third (f 1) (f 2) (f 0) (f 3) e12 e01 e02 e13.symm e23.symm
  have c06 : f 0 = f 6 := fin3_third (f 4) (f 5) (f 0) (f 6) e45 e04 e05 e46.symm e56.symm
  exact e36 (c03.symm.trans c06)

set_option maxRecDepth 4000 in
/-- Every spindle edge is realized as a unit distance in the plane. -/
theorem edge_unit (i j : Fin 7) (h : isEdge i j = true) :
    dist (pt i) (pt j) = 1 := by
  fin_cases i <;> fin_cases j <;>
    first
      | (exfalso; revert h; decide)
      | exact dist01 | exact dist02 | exact dist12 | exact dist13 | exact dist23
      | exact dist04 | exact dist05 | exact dist45 | exact dist46 | exact dist56
      | exact dist36

/-! ### Main result -/

/-- **χ(ℝ²) ≥ 4 (Moser spindle, fully verified, 0 axioms).**

No colouring of the plane with 3 colours can avoid monochromatic unit-distance
pairs: for every `c : Plane → Fin 3` there are two points `p, q` at distance `1`
with `c p = c q`.

Restricting any such colouring to the 7 Moser-spindle vertices yields a
3-colouring of the spindle, which `spindle_not_3colorable` forbids; the
offending edge is a genuine unit distance by `edge_unit`. -/
theorem chromatic_plane_ge_four (c : Plane → Fin 3) :
    ∃ p q : Plane, dist p q = 1 ∧ c p = c q := by
  obtain ⟨i, j, he, hcol⟩ := spindle_not_3colorable (fun k => c (pt k))
  exact ⟨pt i, pt j, edge_unit i j he, hcol⟩

/-- Restatement matching the parent file's phrasing of chromatic lower bounds:
    no proper 3-colouring of the unit-distance graph on the plane exists. This is
    the **verified** companion to the parent's *axiomatized* de Grey bound
    (`hadwiger_nelson_lower_bound`, `χ(ℝ²) ≥ 5`). -/
theorem no_proper_3coloring_of_plane :
    ¬ ∃ c : Plane → Fin 3, ∀ p q : Plane, dist p q = 1 → c p ≠ c q := by
  rintro ⟨c, hc⟩
  obtain ⟨p, q, hd, hcol⟩ := chromatic_plane_ge_four c
  exact hc p q hd hcol

end

end UnitDistanceIndependenceOQ01
