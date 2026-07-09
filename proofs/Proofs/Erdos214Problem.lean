/-
Erdős Problem #214: Unit Distance Free Sets and Unit Squares

Source: https://erdosproblems.com/214
Status: SOLVED (Juhász, 1979)

Statement:
Let S ⊂ ℝ² be such that no two points in S are distance 1 apart.
Must the complement of S contain four points which form a unit square?

Answer: YES (Juhász, 1979)
Juhász proved the complement must contain a congruent copy of any 4-point set,
hence in particular a unit square.

Generalization:
- Complement contains any 4-point configuration
- NOT true for arbitrarily large point sets
- May still hold for any 5-point configuration (open)

References:
- [Er83c] Erdős (1983) - Original problem
- [Ju79] Juhász (1979) - Solution

Tags: geometry, unit-distance, combinatorial-geometry, solved
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic

open Real

namespace Erdos214

/-
## Part 1: Basic Definitions
-/

/-- The Euclidean plane ℝ² -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The Euclidean distance between two points in the plane -/
noncomputable def dist (p q : Plane) : ℝ :=
  ‖p - q‖

/-- A set S is unit-distance-free if no two points are exactly distance 1 apart -/
def IsUnitDistanceFree (S : Set Plane) : Prop :=
  ∀ p q : Plane, p ∈ S → q ∈ S → p ≠ q → dist p q ≠ 1

/-- Four points form a unit square -/
def IsUnitSquare (p₁ p₂ p₃ p₄ : Plane) : Prop :=
  -- All four edges have length 1
  dist p₁ p₂ = 1 ∧ dist p₂ p₃ = 1 ∧ dist p₃ p₄ = 1 ∧ dist p₄ p₁ = 1 ∧
  -- Both diagonals have length √2
  dist p₁ p₃ = Real.sqrt 2 ∧ dist p₂ p₄ = Real.sqrt 2

/-- A set contains a unit square -/
def ContainsUnitSquare (S : Set Plane) : Prop :=
  ∃ p₁ p₂ p₃ p₄ : Plane, p₁ ∈ S ∧ p₂ ∈ S ∧ p₃ ∈ S ∧ p₄ ∈ S ∧
    IsUnitSquare p₁ p₂ p₃ p₄

/-
## Part 2: The Main Statement
-/

/-- Erdős Problem #214: Unit-distance-free sets have complements containing unit squares -/
def Erdos214Statement : Prop :=
  ∀ S : Set Plane, IsUnitDistanceFree S → ContainsUnitSquare Sᶜ

/- Juhász's Theorem (1979): Affirmatively resolves Problem #214.

NOTE: This is *not* assumed as a separate axiom.  It is derived below
(`juhasz_1979`) from the single stronger axiom `juhasz_stronger` via the proved
reduction `unit_square_from_stronger`, so the file rests on exactly one
mathematical assumption (Juhász's 4-point theorem) rather than two.  The main
theorem `erdos_214_solved` and the summary are stated after that derivation. -/

/-
## Part 3: Stronger Version - Any 4-Point Set
-/

/-- A finite set of points in the plane -/
def PointSet (n : ℕ) := Fin n → Plane

/-- A set contains a congruent copy of a point configuration -/
def ContainsCongruentCopy (S : Set Plane) (P : PointSet n) : Prop :=
  ∃ f : Plane → Plane,
    -- f is an isometry (distance-preserving)
    (∀ x y : Plane, dist (f x) (f y) = dist x y) ∧
    -- The image of P lies in S
    (∀ i : Fin n, f (P i) ∈ S)

/-- Juhász's stronger theorem: complement contains any 4-point configuration -/
def JuhaszStrongerTheorem : Prop :=
  ∀ S : Set Plane, IsUnitDistanceFree S →
    ∀ P : PointSet 4, ContainsCongruentCopy Sᶜ P

/-- Juhász proved the stronger result -/
axiom juhasz_stronger : JuhaszStrongerTheorem

/-- Distance between two explicit points of the plane, in coordinates:
    `dist (a,b) (c,d) = √((a-c)² + (b-d)²)`.  Lets the concrete unit square
    below be checked by `norm_num`. -/
theorem dist_coords (a b c d : ℝ) :
    Erdos214.dist (!₂[a, b] : Plane) (!₂[c, d] : Plane)
      = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  unfold Erdos214.dist
  rw [← dist_eq_norm, EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs]

/-- Distance between two arbitrary plane points via their coordinates:
    `dist p q = √((p₀-q₀)² + (p₁-q₁)²)`. The coordinate form of `dist_coords`,
    used to reason about the scaled lattice below. -/
theorem dist_sq (p q : Plane) :
    Erdos214.dist p q = Real.sqrt ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) := by
  unfold Erdos214.dist
  rw [← dist_eq_norm, EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]

/-- The standard unit square `(0,0),(1,0),(1,1),(0,1)` really is a unit square. -/
theorem isUnitSquare_standard :
    IsUnitSquare (!₂[0, 0] : Plane) (!₂[1, 0]) (!₂[1, 1]) (!₂[0, 1]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [dist_coords] <;> norm_num [Real.sqrt_one]

/-- Unit square is a special case of 4-point configurations.  Apply Juhász's
stronger theorem to the standard unit square `P`; the resulting congruent copy
in `Sᶜ` is again a unit square because the witnessing map is an isometry
(distance-preserving), so it carries `P`'s edge/diagonal lengths verbatim. -/
theorem unit_square_from_stronger :
    JuhaszStrongerTheorem → Erdos214Statement := by
  intro hStrong S hFree
  -- The standard unit square as a 4-point configuration.
  set P : PointSet 4 := ![!₂[0, 0], !₂[1, 0], !₂[1, 1], !₂[0, 1]] with hP
  -- Juhász's stronger theorem gives a congruent copy of `P` inside `Sᶜ`.
  obtain ⟨f, hf_isom, hf_mem⟩ := hStrong S hFree P
  -- Its edge/diagonal lengths equal those of `P` (isometry), so it is a unit square.
  obtain ⟨h01, h12, h23, h30, h02, h13⟩ := isUnitSquare_standard
  refine ⟨f (P 0), f (P 1), f (P 2), f (P 3), hf_mem 0, hf_mem 1, hf_mem 2, hf_mem 3,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf_isom, hP]; exact h01
  · rw [hf_isom, hP]; exact h12
  · rw [hf_isom, hP]; exact h23
  · rw [hf_isom, hP]; exact h30
  · rw [hf_isom, hP]; exact h02
  · rw [hf_isom, hP]; exact h13

/-- Juhász's 1979 theorem, **derived** from the stronger 4-point theorem rather
than assumed.  Since `juhasz_stronger` supplies a congruent copy of *any* 4-point
configuration in the complement, `unit_square_from_stronger` specialises it to the
unit square, so the original Problem #214 statement follows with no extra axiom. -/
theorem juhasz_1979 : Erdos214Statement := unit_square_from_stronger juhasz_stronger

/-- The main theorem: Problem #214 is solved -/
theorem erdos_214_solved : Erdos214Statement := juhasz_1979

/-
## Part 4: Limitations for Larger Sets
-/

/-- However, it may hold for 5 points (open question) -/
def HoldsFor5Points : Prop :=
  ∀ S : Set Plane, IsUnitDistanceFree S →
    ∀ P : PointSet 5, ContainsCongruentCopy Sᶜ P

/- The 5-point case is open -/

/-
## Part 5: Connection to Unit Distance Graphs
-/

/-- The unit distance graph: vertices are points, edges connect distance-1 pairs -/
def UnitDistanceGraph (S : Set Plane) : Set (Plane × Plane) :=
  {pq | pq.1 ∈ S ∧ pq.2 ∈ S ∧ pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = 1}

/-- S is unit-distance-free iff its unit distance graph has no edges -/
theorem unit_distance_free_iff_no_edges (S : Set Plane) :
    IsUnitDistanceFree S ↔ UnitDistanceGraph S = ∅ := by
  constructor
  · intro hFree
    ext ⟨p, q⟩
    simp only [Set.mem_empty_iff_false, iff_false]
    intro ⟨hp, hq, hne, hdist⟩
    exact hFree p q hp hq hne hdist
  · intro hEmpty p q hp hq hne hdist
    have : (p, q) ∈ UnitDistanceGraph S := ⟨hp, hq, hne, hdist⟩
    rw [hEmpty] at this
    exact this

/-
## Part 6: Proof Techniques
-/

/-
## Part 7: Examples and Constructions
-/

/-- A proper example: scale ℤ² by √2 -/
def ScaledLattice : Set Plane :=
  {p : Plane | ∃ a b : ℤ, p 0 = Real.sqrt 2 * a ∧ p 1 = Real.sqrt 2 * b}

/-- **The scaled lattice `√2·ℤ²` is unit-distance-free.**

Two distinct lattice points `(√2·a₁, √2·b₁)`, `(√2·a₂, √2·b₂)` are at squared
distance `2·((a₁-a₂)² + (b₁-b₂)²)`, twice a nonnegative integer. If that distance
equalled `1` we would need `2·m = 1` for an integer `m`, impossible. This exhibits
an explicit *infinite* unit-distance-free set, so the hypothesis of Problem #214 is
non-vacuous. -/
theorem scaledLattice_unitDistanceFree : IsUnitDistanceFree ScaledLattice := by
  rintro p q ⟨a₁, b₁, hp0, hp1⟩ ⟨a₂, b₂, hq0, hq1⟩ _ hdist
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hX : (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2
      = ((2 * ((a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2) : ℤ) : ℝ) := by
    rw [hp0, hp1, hq0, hq1]; push_cast; nlinarith [h2]
  rw [dist_sq, hX, Real.sqrt_eq_one] at hdist
  have hint : (2 * ((a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2) : ℤ) = 1 := by exact_mod_cast hdist
  omega

/-
## Part 8: Related Problems
-/

/-
## Part 9: Geometric Intuition
-/

/-
## Part 10: Summary
-/

/-- Erdős Problem #214 is SOLVED -/
theorem erdos_214_status : Erdos214Statement := juhasz_1979

/-- **Erdős Problem #214: SOLVED (Juhász, 1979)**

PROBLEM: If S ⊂ ℝ² has no two points at distance 1,
must Sᶜ contain four points forming a unit square?

ANSWER: YES

PROVED BY: Juhász (1979)

STRONGER RESULT: The complement contains a congruent copy of ANY 4-point set.

LIMITATIONS: This fails for sufficiently large point sets.

OPEN QUESTION: Does it hold for all 5-point configurations?

KEY INSIGHT: Unit-distance-free sets are "sparse" enough that their
complements contain small geometric configurations.
-/
theorem erdos_214_summary :
    -- Main result
    Erdos214Statement ∧
    -- Stronger version for any 4 points
    JuhaszStrongerTheorem := by
  exact ⟨juhasz_1979, juhasz_stronger⟩

/-- Problem status -/
def erdos_214_status_str : String :=
  "SOLVED (Juhász 1979) - Unit-distance-free sets have complements containing unit squares"

/-
## Part 11: Metric Helpers and Structural Facts about Unit Squares

The reduction above (`unit_square_from_stronger`) rests on two geometric facts that
were used *inline*: that an isometry carries a unit square to a unit square, and that
`dist p p = 0`. Here we extract these as reusable, named results and derive two
genuinely new structural consequences: every unit square has four pairwise-distinct
vertices, and hence the complement of a unit-distance-free set contains a unit square
on four *distinct* points — sharpening the problem's "four points" phrasing.
-/

/-- The coordinate distance vanishes exactly on the diagonal: `dist p p = 0`. -/
theorem dist_self (p : Plane) : dist p p = 0 := by
  unfold dist
  rw [sub_self, norm_zero]

/-- The coordinate distance is symmetric: `dist p q = dist q p`. -/
theorem dist_comm (p q : Plane) : dist p q = dist q p := by
  unfold dist
  rw [← neg_sub q p, norm_neg]

/-- **Isometry invariance of unit squares.** If `f` preserves distances then it maps
any unit square to a unit square. This is the geometric heart of the reduction from
Juhász's stronger 4-point theorem: a *congruent copy* of the standard unit square is
again a unit square precisely because the witnessing map is distance-preserving. -/
theorem isUnitSquare_of_isometry {f : Plane → Plane}
    (hf : ∀ x y : Plane, dist (f x) (f y) = dist x y)
    {p₁ p₂ p₃ p₄ : Plane} (h : IsUnitSquare p₁ p₂ p₃ p₄) :
    IsUnitSquare (f p₁) (f p₂) (f p₃) (f p₄) := by
  obtain ⟨h12, h23, h34, h41, h13, h24⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hf]
  exacts [h12, h23, h34, h41, h13, h24]

/-- **A unit square has four pairwise-distinct vertices.** The four edges have length
`1 ≠ 0` and the two diagonals have length `√2 ≠ 0`, and `dist p p = 0`, so no two of
the six vertex pairs can coincide. This certifies that `ContainsUnitSquare` really is
a statement about four genuinely distinct points, not a degenerate configuration. -/
theorem IsUnitSquare.distinct {p₁ p₂ p₃ p₄ : Plane} (h : IsUnitSquare p₁ p₂ p₃ p₄) :
    p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₃ ≠ p₄ ∧ p₄ ≠ p₁ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₄ := by
  obtain ⟨h12, h23, h34, h41, h13, h24⟩ := h
  have hedge : ∀ p q : Plane, dist p q = 1 → p ≠ q := by
    rintro p q hd rfl
    rw [dist_self] at hd
    norm_num at hd
  have hdiag : ∀ p q : Plane, dist p q = Real.sqrt 2 → p ≠ q := by
    rintro p q hd rfl
    rw [dist_self] at hd
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  exact ⟨hedge _ _ h12, hedge _ _ h23, hedge _ _ h34, hedge _ _ h41,
    hdiag _ _ h13, hdiag _ _ h24⟩

/-- **Capstone.** The complement of any unit-distance-free set contains a unit square
on four *pairwise-distinct* points. Combines the solved statement `erdos_214_solved`
with the vertex-distinctness of unit squares. -/
theorem complement_contains_distinct_unit_square
    (S : Set Plane) (hS : IsUnitDistanceFree S) :
    ∃ p₁ p₂ p₃ p₄ : Plane,
      p₁ ∈ Sᶜ ∧ p₂ ∈ Sᶜ ∧ p₃ ∈ Sᶜ ∧ p₄ ∈ Sᶜ ∧
      IsUnitSquare p₁ p₂ p₃ p₄ ∧
      p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₃ ≠ p₄ ∧ p₄ ≠ p₁ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₄ := by
  obtain ⟨p₁, p₂, p₃, p₄, h1, h2, h3, h4, hsq⟩ := erdos_214_solved S hS
  obtain ⟨d12, d23, d34, d41, d13, d24⟩ := hsq.distinct
  exact ⟨p₁, p₂, p₃, p₄, h1, h2, h3, h4, hsq, d12, d23, d34, d41, d13, d24⟩

/-
## Part 12: The coordinate distance is a genuine metric; the scaled lattice is infinite

Two further axiom-free strengthenings, independent of the Juhász input.

First, `Erdos214.dist` is `‖p - q‖`, so it inherits the two metric axioms missing from
the earlier `dist_self` / `dist_comm` pair: non-negativity (`norm_nonneg`) and the
triangle inequality (`norm_add_le`).  Together with `dist_self` and `dist_comm` this
certifies `Erdos214.dist` really is a metric.

Second, `scaledLattice_unitDistanceFree` exhibits a unit-distance-free set, but only
guarantees it is non-empty.  Here we show `√2·ℤ²` is in fact *infinite*: the horizontal
axis `{(√2·n, 0) : n ∈ ℤ}` already embeds `ℤ`.  So Problem #214's hypothesis is satisfied
by an explicit infinite family, not merely a single configuration.
-/

/-- **Non-negativity of the coordinate distance.** A metric axiom: `dist p q = ‖p - q‖ ≥ 0`. -/
theorem dist_nonneg (p q : Plane) : 0 ≤ dist p q := by
  unfold dist
  exact norm_nonneg _

/-- **Triangle inequality for the coordinate distance.** The last metric axiom: writing
`p - r = (p - q) + (q - r)` and applying `norm_add_le`.  With `dist_self`, `dist_comm`
and `dist_nonneg` this shows `Erdos214.dist` is a genuine metric. -/
theorem dist_triangle (p q r : Plane) : dist p r ≤ dist p q + dist q r := by
  unfold dist
  calc ‖p - r‖ = ‖(p - q) + (q - r)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖p - q‖ + ‖q - r‖ := norm_add_le _ _

/-- The point `(√2·n, 0)` lies in the scaled lattice for every integer `n`
(take lattice coordinates `a = n`, `b = 0`). -/
theorem scaledLattice_horiz_mem (n : ℤ) :
    (!₂[Real.sqrt 2 * (n : ℝ), 0] : Plane) ∈ ScaledLattice := by
  refine ⟨n, 0, ?_, ?_⟩ <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **The scaled lattice `√2·ℤ²` is infinite.** The horizontal embedding
`n ↦ (√2·n, 0)` is injective (because `√2 ≠ 0`) and lands in the lattice, so the lattice
contains a copy of `ℤ`.  This sharpens `scaledLattice_unitDistanceFree`: Problem #214's
hypothesis is realised by an explicit *infinite* unit-distance-free set. -/
theorem scaledLattice_infinite : ScaledLattice.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℤ => (!₂[Real.sqrt 2 * (n : ℝ), 0] : Plane))
  · -- injectivity: recover `n` from the first coordinate `√2·n`
    intro m n hmn
    have hmn' : (!₂[Real.sqrt 2 * (m : ℝ), 0] : Plane)
        = !₂[Real.sqrt 2 * (n : ℝ), 0] := hmn
    have h0 : Real.sqrt 2 * (m : ℝ) = Real.sqrt 2 * (n : ℝ) := by
      have hc := congrArg (fun x : Plane => x 0) hmn'
      simpa [Matrix.cons_val_zero] using hc
    have hs : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast mul_left_cancel₀ hs h0
  · exact scaledLattice_horiz_mem

end Erdos214
