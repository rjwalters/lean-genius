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

/-- At perfect squares, g achieves k (axiom: requires k×k grid construction) -/
axiom g_ap_perfect_square : ∀ k : ℕ, k ≥ 1 → g_ap (k ^ 2) = k

/- ## Axiom Elimination: g_ap_bounded and f_rot_perfect_square

We derive these from f_rot_bounded + g_ap_perfect_square + the structural
relationship g_ap ≤ f_rot (every axis-parallel packing is a general packing).
-/

section AxiomElimination

/-- The center of a rotated square is in its closure -/
private lemma center_in_closure (sq : RotatedSquare) :
    sq.center ∈ sq.closure' := by
  simp only [RotatedSquare.closure', Set.mem_setOf_eq]
  simp [abs_of_nonneg, le_div_iff₀]
  constructor <;> positivity

/-- Edge midpoint at rotated coords (s/2, 0) is in the closure.
    World coords: (c₁ + s/2·cos θ, c₂ + s/2·sin θ). -/
private lemma midpoint_pos_cos_mem_closure (sq : RotatedSquare) :
    (sq.center.1 + sq.side / 2 * Real.cos sq.angle,
     sq.center.2 + sq.side / 2 * Real.sin sq.angle) ∈ sq.closure' := by
  simp only [RotatedSquare.closure', Set.mem_setOf_eq]
  set h := sq.side / 2
  set θ := sq.angle
  -- rx = (h cos θ) cos θ + (h sin θ) sin θ = h(cos²θ + sin²θ) = h
  -- ry = -(h cos θ) sin θ + (h sin θ) cos θ = 0
  have hrx : h * Real.cos θ * Real.cos θ + h * Real.sin θ * Real.sin θ = h := by
    have := Real.sin_sq_add_cos_sq θ; nlinarith [sq_abs (Real.cos θ), sq_abs (Real.sin θ)]
  have hry : -(h * Real.cos θ) * Real.sin θ + h * Real.sin θ * Real.cos θ = 0 := by ring
  rw [hrx, hry]
  exact ⟨le_abs_self h, by rw [abs_zero]; positivity⟩

/-- Opposite edge midpoint at rotated coords (-s/2, 0) is in the closure. -/
private lemma midpoint_neg_cos_mem_closure (sq : RotatedSquare) :
    (sq.center.1 - sq.side / 2 * Real.cos sq.angle,
     sq.center.2 - sq.side / 2 * Real.sin sq.angle) ∈ sq.closure' := by
  simp only [RotatedSquare.closure', Set.mem_setOf_eq]
  set h := sq.side / 2
  set θ := sq.angle
  have hrx : (-h * Real.cos θ) * Real.cos θ + (-h * Real.sin θ) * Real.sin θ = -h := by
    have := Real.sin_sq_add_cos_sq θ; nlinarith [sq_abs (Real.cos θ), sq_abs (Real.sin θ)]
  have hry : -(-h * Real.cos θ) * Real.sin θ + (-h * Real.sin θ) * Real.cos θ = 0 := by ring
  rw [show sq.center.1 - h * Real.cos θ - sq.center.1 = -h * Real.cos θ from by ring,
      show sq.center.2 - h * Real.sin θ - sq.center.2 = -h * Real.sin θ from by ring,
      hrx, hry]
  constructor
  · rw [abs_neg]; exact le_abs_self h
  · rw [abs_zero]; positivity

/-- Edge midpoint at rotated coords (0, s/2) is in the closure. -/
private lemma midpoint_pos_sin_mem_closure (sq : RotatedSquare) :
    (sq.center.1 - sq.side / 2 * Real.sin sq.angle,
     sq.center.2 + sq.side / 2 * Real.cos sq.angle) ∈ sq.closure' := by
  simp only [RotatedSquare.closure', Set.mem_setOf_eq]
  set h := sq.side / 2
  set θ := sq.angle
  have hrx : (-h * Real.sin θ) * Real.cos θ + (h * Real.cos θ) * Real.sin θ = 0 := by ring
  have hry : -(-h * Real.sin θ) * Real.sin θ + (h * Real.cos θ) * Real.cos θ = h := by
    have := Real.sin_sq_add_cos_sq θ; nlinarith [sq_abs (Real.cos θ), sq_abs (Real.sin θ)]
  rw [show sq.center.1 - h * Real.sin θ - sq.center.1 = -h * Real.sin θ from by ring,
      show sq.center.2 + h * Real.cos θ - sq.center.2 = h * Real.cos θ from by ring,
      hrx, hry]
  exact ⟨by rw [abs_zero]; positivity, le_abs_self h⟩

/-- Opposite edge midpoint at rotated coords (0, -s/2). -/
private lemma midpoint_neg_sin_mem_closure (sq : RotatedSquare) :
    (sq.center.1 + sq.side / 2 * Real.sin sq.angle,
     sq.center.2 - sq.side / 2 * Real.cos sq.angle) ∈ sq.closure' := by
  simp only [RotatedSquare.closure', Set.mem_setOf_eq]
  set h := sq.side / 2
  set θ := sq.angle
  have hrx : (h * Real.sin θ) * Real.cos θ + (-h * Real.cos θ) * Real.sin θ = 0 := by ring
  have hry : -(h * Real.sin θ) * Real.sin θ + (-h * Real.cos θ) * Real.cos θ = -h := by
    have := Real.sin_sq_add_cos_sq θ; nlinarith [sq_abs (Real.cos θ), sq_abs (Real.sin θ)]
  rw [show sq.center.1 + h * Real.sin θ - sq.center.1 = h * Real.sin θ from by ring,
      show sq.center.2 - h * Real.cos θ - sq.center.2 = -h * Real.cos θ from by ring,
      hrx, hry]
  constructor
  · rw [abs_zero]; positivity
  · rw [abs_neg]; exact le_abs_self h

/-- s · |cos θ| ≤ 1 for a rotated square contained in [0,1]².
    Proof: opposite edge midpoints are in [0,1]², their x-coord difference = s cos θ. -/
private lemma side_mul_abs_cos_le_one (sq : RotatedSquare) (h : sq.ContainedInUnit) :
    sq.side * |Real.cos sq.angle| ≤ 1 := by
  have h1 := h (midpoint_pos_cos_mem_closure sq)
  have h2 := h (midpoint_neg_cos_mem_closure sq)
  simp only [unitSquare', Set.mem_setOf_eq] at h1 h2
  -- h1.1: 0 ≤ c₁ + s/2 cos θ, h1.2.1: c₁ + s/2 cos θ ≤ 1
  -- h2.1: 0 ≤ c₁ - s/2 cos θ, h2.2.1: c₁ - s/2 cos θ ≤ 1
  -- So: s cos θ = (c₁ + s/2 cos θ) - (c₁ - s/2 cos θ) and both are in [0,1]
  have hcos := sq.side / 2 * Real.cos sq.angle
  rw [show sq.side * |Real.cos sq.angle| = |sq.side * Real.cos sq.angle| from by
    rw [abs_mul, abs_of_pos sq.side_pos]]
  rw [show sq.side * Real.cos sq.angle =
    (sq.center.1 + sq.side / 2 * Real.cos sq.angle) -
    (sq.center.1 - sq.side / 2 * Real.cos sq.angle) from by ring]
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2.1, h2.1, h2.2.1]

/-- s · |sin θ| ≤ 1 for a rotated square contained in [0,1]².
    Same argument using the other pair of edge midpoints. -/
private lemma side_mul_abs_sin_le_one (sq : RotatedSquare) (h : sq.ContainedInUnit) :
    sq.side * |Real.sin sq.angle| ≤ 1 := by
  have h1 := h (midpoint_pos_sin_mem_closure sq)
  have h2 := h (midpoint_neg_sin_mem_closure sq)
  simp only [unitSquare', Set.mem_setOf_eq] at h1 h2
  rw [show sq.side * |Real.sin sq.angle| = |sq.side * Real.sin sq.angle| from by
    rw [abs_mul, abs_of_pos sq.side_pos]]
  rw [show sq.side * Real.sin sq.angle =
    (sq.center.1 + sq.side / 2 * Real.sin sq.angle) -
    (sq.center.1 - sq.side / 2 * Real.sin sq.angle) from by ring]
  -- Wait: the sin midpoints differ in x-coord by -s sin θ
  -- midpoint_pos_sin: x = c₁ - s/2 sin θ
  -- midpoint_neg_sin: x = c₁ + s/2 sin θ
  -- Difference (neg - pos) = s sin θ
  rw [show (sq.center.1 + sq.side / 2 * Real.sin sq.angle) -
    (sq.center.1 - sq.side / 2 * Real.sin sq.angle) =
    sq.side * Real.sin sq.angle from by ring]
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2.1, h2.1, h2.2.1]

/-- A rotated square contained in [0,1]² has side ≤ √2.
    Proof: s²cos²θ ≤ 1 and s²sin²θ ≤ 1, so s² = s²(cos²θ+sin²θ) ≤ 2. -/
theorem side_le_sqrt_two (sq : RotatedSquare) (h : sq.ContainedInUnit) :
    sq.side ≤ Real.sqrt 2 := by
  have hcos := side_mul_abs_cos_le_one sq h
  have hsin := side_mul_abs_sin_le_one sq h
  have h1 : (sq.side * |Real.cos sq.angle|) ^ 2 ≤ 1 := by nlinarith
  have h2 : (sq.side * |Real.sin sq.angle|) ^ 2 ≤ 1 := by nlinarith
  have hsq : sq.side ^ 2 ≤ 2 := by
    have := Real.sin_sq_add_cos_sq sq.angle
    nlinarith [sq_abs (sq.side * Real.cos sq.angle),
               sq_abs (sq.side * Real.sin sq.angle),
               sq_abs (Real.cos sq.angle), sq_abs (Real.sin sq.angle)]
  rwa [← Real.sqrt_le_sqrt (by positivity : 0 ≤ sq.side ^ 2),
       Real.sqrt_sq (le_of_lt sq.side_pos)]

/-- The set of achievable sums for general packings is bounded above -/
private lemma f_rot_set_bddAbove (n : ℕ) :
    BddAbove {s : ℝ | ∃ P : GeneralPacking n, P.sumSides = s} := by
  use n * Real.sqrt 2
  intro s ⟨P, hP⟩
  rw [← hP]
  unfold GeneralPacking.sumSides
  calc ∑ i : Fin n, (P.squares i).side
      ≤ ∑ _i : Fin n, Real.sqrt 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact side_le_sqrt_two (P.squares i) (P.contained i)
    _ = n * Real.sqrt 2 := by simp [Finset.sum_const, Finset.card_fin]

/-- The achievable AP sum set is nonempty.
    Proof: construct n axis-parallel squares of side 1/(n+1), angle 0,
    centered at ((2i+1)/(2(n+1)), 1/(2(n+1))) for i = 0..n-1. -/
private lemma g_ap_set_nonempty (n : ℕ) :
    {s : ℝ | ∃ P : AxisParallelPacking n, P.sumSides = s}.Nonempty := by
  -- Place n tiny squares in a row along the bottom of [0,1]²
  set m : ℝ := ↑n + 1 with hm_def
  have hm : 0 < m := by positivity
  have h2m : 0 < 2 * m := by positivity
  refine ⟨_, ⟨{
    squares := fun i =>
      ⟨((2 * (↑(i : ℕ) : ℝ) + 1) / (2 * m), 1 / (2 * m)), 1 / m, 0, by positivity⟩
    contained := fun i p hp => by
      simp only [RotatedSquare.ContainedInUnit, RotatedSquare.closure', unitSquare',
        Real.cos_zero, Real.sin_zero, mul_one, mul_zero, add_zero, zero_add,
        neg_zero, Set.mem_setOf_eq] at hp ⊢
      obtain ⟨hpx, hpy⟩ := hp
      have half_eq : (1 : ℝ) / m / 2 = 1 / (2 * m) := div_div 1 m 2
      rw [half_eq] at hpx hpy
      rw [abs_le] at hpx hpy
      have hi_nn : (0 : ℝ) ≤ ↑(i : ℕ) := Nat.cast_nonneg _
      have hi_lt : (↑(i : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- 0 ≤ p.1: From hpx.1, p.1 ≥ (2i+1)/(2m) - 1/(2m) = i/m ≥ 0
        have h1 : (2 * (↑(i : ℕ) : ℝ) + 1 - 1) / (2 * m) ≤ p.1 := by
          rw [sub_div]; linarith
        have h2 : (2 * (↑(i : ℕ) : ℝ)) / (2 * m) ≥ 0 := div_nonneg (by nlinarith) (le_of_lt h2m)
        linarith [show 2 * (↑(i : ℕ) : ℝ) + 1 - 1 = 2 * ↑(i : ℕ) from by ring]
      · -- p.1 ≤ 1: From hpx.2, p.1 ≤ (2i+2)/(2m) = (i+1)/m ≤ 1
        have h1 : p.1 ≤ (2 * (↑(i : ℕ) : ℝ) + 1 + 1) / (2 * m) := by
          rw [add_div]; linarith
        have h2 : (2 * (↑(i : ℕ) : ℝ) + 2) / (2 * m) ≤ 1 := by
          rw [div_le_one h2m]; nlinarith
        linarith [show 2 * (↑(i : ℕ) : ℝ) + 1 + 1 = 2 * ↑(i : ℕ) + 2 from by ring]
      · -- 0 ≤ p.2: From hpy.1, p.2 ≥ 1/(2m) - 1/(2m) = 0
        linarith
      · -- p.2 ≤ 1: From hpy.2, p.2 ≤ 1/(2m) + 1/(2m) = 1/m ≤ 1
        have h1 : 1 / (2 * m) + 1 / (2 * m) = 1 / m := by ring
        have h2 : 1 / m ≤ 1 := div_le_one_of_le (by linarith) (le_of_lt hm)
        linarith
    disjoint := fun i j hij => by
      simp only [RotatedSquare.DisjointInteriors, RotatedSquare.interior,
        Real.cos_zero, Real.sin_zero, mul_one, mul_zero, add_zero, zero_add,
        neg_zero, Set.disjoint_left, Set.mem_setOf_eq]
      intro p ⟨hxi, _⟩ ⟨hxj, _⟩
      have half_eq : (1 : ℝ) / m / 2 = 1 / (2 * m) := div_div 1 m 2
      rw [half_eq] at hxi hxj
      rw [abs_lt] at hxi hxj
      -- i ≠ j as ℕ implies |i - j| ≥ 1, so x-ranges don't overlap
      have hij_val : (i : ℕ) ≠ (j : ℕ) := Fin.val_ne_of_ne hij
      rcases Nat.lt_or_gt_of_ne hij_val with h | h
      · -- i < j: p.1 < (2i+2)/(2m) and (2j)/(2m) < p.1, but 2j ≥ 2i+2
        have : (↑(j : ℕ) : ℝ) ≥ (↑(i : ℕ) : ℝ) + 1 := by exact_mod_cast h
        have hxu : p.1 < (2 * (↑(i : ℕ) : ℝ) + 1 + 1) / (2 * m) := by rw [add_div]; linarith
        have hxl : (2 * (↑(j : ℕ) : ℝ) + 1 - 1) / (2 * m) < p.1 := by rw [sub_div]; linarith
        nlinarith [show 2 * (↑(i : ℕ) : ℝ) + 1 + 1 = 2 * (↑(i : ℕ) : ℝ) + 2 from by ring,
                   show 2 * (↑(j : ℕ) : ℝ) + 1 - 1 = 2 * (↑(j : ℕ) : ℝ) from by ring]
      · -- j < i: symmetric
        have : (↑(i : ℕ) : ℝ) ≥ (↑(j : ℕ) : ℝ) + 1 := by exact_mod_cast h
        have hxu : p.1 < (2 * (↑(j : ℕ) : ℝ) + 1 + 1) / (2 * m) := by rw [add_div]; linarith
        have hxl : (2 * (↑(i : ℕ) : ℝ) + 1 - 1) / (2 * m) < p.1 := by rw [sub_div]; linarith
        nlinarith [show 2 * (↑(j : ℕ) : ℝ) + 1 + 1 = 2 * (↑(j : ℕ) : ℝ) + 2 from by ring,
                   show 2 * (↑(i : ℕ) : ℝ) + 1 - 1 = 2 * (↑(i : ℕ) : ℝ) from by ring]
    axisParallel := fun _ => rfl }, rfl⟩⟩

/-- g_ap(n) ≤ f_rot(n): every axis-parallel packing is a general packing -/
theorem g_ap_le_f_rot (n : ℕ) : g_ap n ≤ f_rot n := by
  unfold g_ap f_rot
  exact csSup_le_csSup (f_rot_set_bddAbove n) (g_ap_set_nonempty n) (achievable_sums_subset n)

/-- g is bounded above by √n (PROVED, was axiom).
    Follows from g_ap ≤ f_rot ≤ √n. -/
theorem g_ap_bounded (n : ℕ) : g_ap n ≤ Real.sqrt n :=
  le_trans (g_ap_le_f_rot n) (f_rot_bounded n)

/-- At perfect squares, f_rot achieves k (PROVED from g_ap_perfect_square + f_rot_bounded).
    Upper bound: f_rot(k²) ≤ √(k²) = k.
    Lower bound: g_ap(k²) = k and g_ap ≤ f_rot. -/
theorem f_rot_perfect_square (k : ℕ) (hk : k ≥ 1) : f_rot (k ^ 2) = k := by
  apply le_antisymm
  · -- f_rot(k²) ≤ √(k²) = k
    have h := f_rot_bounded (k ^ 2)
    rwa [show (↑(k ^ 2) : ℝ) = (↑k : ℝ) ^ 2 from by push_cast; ring,
         Real.sqrt_sq (by positivity : (↑k : ℝ) ≥ 0)] at h
  · -- f_rot(k²) ≥ g_ap(k²) = k
    have hg := g_ap_perfect_square k hk
    have hle := g_ap_le_f_rot (k ^ 2)
    linarith

end AxiomElimination

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
