/-
  Open Question: Can Rotated Squares Beat Axis-Parallel Packings?

  Related to Erdős Problem #106 (Square Packing in the Unit Square).

  The BKU theorem (2024) proves g(k²+1) = k for axis-parallel squares.
  The general case remains open: can rotated squares achieve a larger
  total side-length sum than axis-parallel arrangements?

  This file formalizes the question by defining rotated squares,
  general packings, and the relationship f_rot(n) ≥ g(n).

  No example is known where rotation helps.

  References:
  [BKU24] Baek-Koizumi-Ueoro (2024) - axis-parallel case solved
  [ErSo95] Erdős-Soifer, "Squares packing" (1995)

  Tags: discrete-geometry, packing, squares, rotation, open-problem
-/

import Mathlib

open Set Real Finset

/-
## Rotated Squares in the Plane

A rotated square is defined by its center, side length, and rotation angle.
The interior is obtained by rotating the axis-parallel square by the given angle.
-/

/-- A square in the plane, possibly rotated by angle θ -/
structure RotatedSquare where
  center : ℝ × ℝ
  side : ℝ
  angle : ℝ
  side_pos : side > 0

/-- The interior of a rotated square.
    A point is inside if, when rotated back to axis-parallel frame, it lies
    within [-side/2, side/2]² centered at the origin. -/
def RotatedSquare.interior (s : RotatedSquare) : Set (ℝ × ℝ) :=
  {p | let dx := p.1 - s.center.1
       let dy := p.2 - s.center.2
       let rx := dx * Real.cos s.angle + dy * Real.sin s.angle
       let ry := -dx * Real.sin s.angle + dy * Real.cos s.angle
       |rx| < s.side / 2 ∧ |ry| < s.side / 2}

/-- The closure of a rotated square -/
def RotatedSquare.closure' (s : RotatedSquare) : Set (ℝ × ℝ) :=
  {p | let dx := p.1 - s.center.1
       let dy := p.2 - s.center.2
       let rx := dx * Real.cos s.angle + dy * Real.sin s.angle
       let ry := -dx * Real.sin s.angle + dy * Real.cos s.angle
       |rx| ≤ s.side / 2 ∧ |ry| ≤ s.side / 2}

/-- Two rotated squares have disjoint interiors -/
def RotatedSquare.DisjointInteriors (s₁ s₂ : RotatedSquare) : Prop :=
  Disjoint s₁.interior s₂.interior

/-
## Axis-Parallel Squares as Special Case

An axis-parallel square is a rotated square with angle = 0.
-/

/-- Construct an axis-parallel square (angle = 0) -/
def RotatedSquare.axisParallel (c : ℝ × ℝ) (s : ℝ) (hs : s > 0) : RotatedSquare :=
  ⟨c, s, 0, hs⟩

/-
## The Unit Square and Containment
-/

/-- The unit square [0,1]² -/
def unitSquare' : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

/-- A rotated square is contained in the unit square -/
def RotatedSquare.ContainedInUnit (s : RotatedSquare) : Prop :=
  s.closure' ⊆ unitSquare'

/-
## General Packings (allowing rotation)
-/

/-- A valid packing of n possibly-rotated squares in the unit square -/
structure GeneralPacking (n : ℕ) where
  squares : Fin n → RotatedSquare
  contained : ∀ i, (squares i).ContainedInUnit
  disjoint : ∀ i j, i ≠ j → (squares i).DisjointInteriors (squares j)

/-- Sum of side lengths in a general packing -/
noncomputable def GeneralPacking.sumSides {n : ℕ} (P : GeneralPacking n) : ℝ :=
  ∑ i : Fin n, (P.squares i).side

/-
## Axis-Parallel Packings (restricted)
-/

/-- A packing where all squares are axis-parallel -/
structure AxisParallelPacking (n : ℕ) extends GeneralPacking n where
  axisParallel : ∀ i, (squares i).angle = 0

/-- Sum of side lengths in an axis-parallel packing -/
noncomputable def AxisParallelPacking.sumSides {n : ℕ} (P : AxisParallelPacking n) : ℝ :=
  P.toGeneralPacking.sumSides

/-
## The Objective Functions
-/

/-- f_rot(n): maximum sum of side lengths allowing rotation -/
noncomputable def f_rot (n : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ P : GeneralPacking n, P.sumSides = s}

/-- g(n): maximum sum of side lengths for axis-parallel packings only -/
noncomputable def g_ap (n : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ P : AxisParallelPacking n, P.sumSides = s}

/-
## Relationship: g(n) ≤ f_rot(n)

Every axis-parallel packing is a general packing, so g(n) ≤ f_rot(n).
-/

/-- An axis-parallel packing is a general packing -/
theorem axis_parallel_is_general {n : ℕ} (P : AxisParallelPacking n) :
    ∃ Q : GeneralPacking n, Q.sumSides = P.sumSides :=
  ⟨P.toGeneralPacking, rfl⟩

/-- The set of achievable sums for axis-parallel packings is a subset of general -/
theorem achievable_sums_subset (n : ℕ) :
    {s : ℝ | ∃ P : AxisParallelPacking n, P.sumSides = s} ⊆
    {s : ℝ | ∃ P : GeneralPacking n, P.sumSides = s} := by
  intro s hs
  obtain ⟨P, hP⟩ := hs
  exact ⟨P.toGeneralPacking, hP⟩

/-
## Area Bound: f_rot(n) ≤ √n

Rotation preserves area: a rotated square with side s has area s².
By disjointness and containment in the unit square, ∑ sᵢ² ≤ 1.
Cauchy-Schwarz then gives (∑ sᵢ)² ≤ n · ∑ sᵢ² ≤ n, so ∑ sᵢ ≤ √n.
-/

/-- The area of a rotated square equals side² (rotation preserves area) -/
axiom rotated_square_area (s : RotatedSquare) :
  MeasureTheory.volume (s.interior) = ENNReal.ofReal (s.side ^ 2)

/-- f_rot is bounded above by √n (Cauchy-Schwarz via area) -/
axiom f_rot_bounded : ∀ n : ℕ, f_rot n ≤ Real.sqrt n

/-- f_rot is monotone increasing -/
axiom f_rot_mono : ∀ n m : ℕ, n ≤ m → f_rot n ≤ f_rot m

/-- g is bounded above by √n -/
axiom g_ap_bounded : ∀ n : ℕ, g_ap n ≤ Real.sqrt n

/-- At perfect squares, both functions achieve k -/
axiom f_rot_perfect_square : ∀ k : ℕ, k ≥ 1 → f_rot (k ^ 2) = k

axiom g_ap_perfect_square : ∀ k : ℕ, k ≥ 1 → g_ap (k ^ 2) = k

/-
## BKU Theorem (axis-parallel case)
-/

/-- BKU (2024): g(k²+1) = k for axis-parallel squares -/
axiom bku_theorem_ap : ∀ k : ℕ, k ≥ 1 → g_ap (k ^ 2 + 1) = k

/-
## Derived Results
-/

/-- f_rot at perfect squares: upper bound from Cauchy-Schwarz -/
theorem f_rot_upper_bound (n : ℕ) : f_rot n ≤ Real.sqrt n :=
  f_rot_bounded n

/-- g at perfect squares: lower bound from k×k grid -/
theorem g_ap_lower_k2_plus_1 (k : ℕ) (hk : k ≥ 1) : g_ap (k ^ 2 + 1) ≥ k := by
  have := bku_theorem_ap k hk
  linarith

/-- f_rot(k²+1) ≥ k: at least as good as axis-parallel -/
theorem f_rot_lower_k2_plus_1 (k : ℕ) (hk : k ≥ 1) : f_rot (k ^ 2 + 1) ≥ k := by
  have h1 : f_rot (k ^ 2) ≤ f_rot (k ^ 2 + 1) := f_rot_mono (k ^ 2) (k ^ 2 + 1) (by omega)
  have h2 := f_rot_perfect_square k hk
  linarith

/-- f_rot(k²+1) ≤ √(k²+1) -/
theorem f_rot_upper_k2_plus_1 (k : ℕ) : f_rot (k ^ 2 + 1) ≤ Real.sqrt (k ^ 2 + 1) :=
  f_rot_bounded (k ^ 2 + 1)

/-
## The Main Open Question

Does there exist n such that rotation strictly helps?
I.e., is f_rot(n) > g(n) for some n?
-/

/-- The open question: can rotation help? -/
def rotationHelps : Prop :=
  ∃ n : ℕ, f_rot n > g_ap n

/-- Equivalently: is there n where axis-parallel is strictly suboptimal? -/
def axisParallelSuboptimal : Prop :=
  ∃ n : ℕ, n ≥ 2 ∧ f_rot n > g_ap n

/-- The stronger claim: rotation never helps -/
def rotationNeverHelps : Prop :=
  ∀ n : ℕ, f_rot n = g_ap n

/-- If rotation never helps, then the main conjecture for general squares
    reduces to the axis-parallel case (BKU) -/
theorem rotation_never_helps_implies_conjecture (h : rotationNeverHelps)
    (k : ℕ) (hk : k ≥ 1) : f_rot (k ^ 2 + 1) = k := by
  rw [h (k ^ 2 + 1)]
  exact bku_theorem_ap k hk

/-
## Equivalence with the General Erdős Conjecture

If rotation never helps, then f(k²+1) = k follows from BKU.
If rotation does help, then the general conjecture is strictly harder.
-/

/-- The general Erdős conjecture in terms of f_rot -/
def erdos106GeneralConjecture : Prop :=
  ∀ k : ℕ, k ≥ 1 → f_rot (k ^ 2 + 1) = k

/-- BKU + rotation_never_helps → general conjecture -/
theorem bku_and_no_rotation_implies_general
    (h : rotationNeverHelps) : erdos106GeneralConjecture := by
  intro k hk
  exact rotation_never_helps_implies_conjecture h k hk

/-- At n = 1, both agree: f_rot(1) = g(1) = 1 -/
theorem agree_at_1 : f_rot 1 = g_ap 1 := by
  have h1 := f_rot_perfect_square 1 (by omega)
  have h2 := g_ap_perfect_square 1 (by omega)
  simp at h1 h2
  rw [h1, h2]

/-- At perfect squares, both agree: f_rot(k²) = g(k²) = k -/
theorem agree_at_perfect_squares (k : ℕ) (hk : k ≥ 1) :
    f_rot (k ^ 2) = g_ap (k ^ 2) := by
  rw [f_rot_perfect_square k hk, g_ap_perfect_square k hk]

/-
## Structural Observations

Key insight: if rotation helps, it must help at non-perfect-square values
of n, since both functions agree at k² for all k.
-/

/-- If rotation ever helps, it can't be at a perfect square -/
theorem rotation_cant_help_at_perfect_square (k : ℕ) (hk : k ≥ 1) :
    f_rot (k ^ 2) = g_ap (k ^ 2) :=
  agree_at_perfect_squares k hk

/-- f_rot(2) = 1: Erdős's original argument extends to rotated squares.
    Two squares (possibly rotated) with disjoint interiors in [0,1]² have
    total side-length sum ≤ 1, achieved by a single unit square. -/
axiom f_rot_2 : f_rot 2 = 1

/-- At n = 2, rotation doesn't help: f_rot(2) = g(2) = 1 -/
theorem no_rotation_help_at_2 : f_rot 2 = g_ap 2 := by
  rw [f_rot_2]
  have h : (2 : ℕ) = 1 ^ 2 + 1 := by norm_num
  rw [h, bku_theorem_ap 1 (by omega)]
  norm_num

#check rotationHelps
#check rotationNeverHelps
#check erdos106GeneralConjecture
