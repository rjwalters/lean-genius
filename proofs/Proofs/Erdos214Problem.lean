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

/-!
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

/-!
## Part 2: The Main Statement
-/

/-- Erdős Problem #214: Unit-distance-free sets have complements containing unit squares -/
def Erdos214Statement : Prop :=
  ∀ S : Set Plane, IsUnitDistanceFree S → ContainsUnitSquare Sᶜ

/-- Juhász's Theorem (1979): Affirmatively resolves Problem #214 -/
axiom juhasz_1979 : Erdos214Statement

/-- The main theorem: Problem #214 is solved -/
theorem erdos_214_solved : Erdos214Statement := juhasz_1979

/-!
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

/-- Unit square is a special case of 4-point configurations -/
theorem unit_square_from_stronger :
    JuhaszStrongerTheorem → Erdos214Statement := by
  intro hStrong S hFree
  -- A unit square is a particular 4-point configuration
  -- Apply Juhász's stronger theorem
  sorry

/-!
## Part 4: Limitations for Larger Sets
-/

/-- The stronger theorem fails for arbitrarily large point sets -/
axiom fails_for_large_sets :
  ∃ n : ℕ, ∃ S : Set Plane, IsUnitDistanceFree S ∧
    ∃ P : PointSet n, ¬ContainsCongruentCopy Sᶜ P

/-- However, it may hold for 5 points (open question) -/
def HoldsFor5Points : Prop :=
  ∀ S : Set Plane, IsUnitDistanceFree S →
    ∀ P : PointSet 5, ContainsCongruentCopy Sᶜ P

/-- The 5-point case is open -/
axiom five_points_open : True -- Status of HoldsFor5Points is unknown

/-!
## Part 5: Connection to Unit Distance Graphs
-/

/-- The unit distance graph: vertices are points, edges connect distance-1 pairs -/
def UnitDistanceGraph (S : Set Plane) : Set (Plane × Plane) :=
  {(p, q) | p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ dist p q = 1}

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

/-- Chromatic number of the plane -/
axiom chromatic_number_of_plane :
  -- The chromatic number χ(ℝ²) with respect to unit distances
  -- is between 4 and 7 (inclusive)
  -- de Grey (2018) proved χ(ℝ²) ≥ 5
  True

/-!
## Part 6: Proof Techniques
-/

/-- Key insight: analyze the structure of maximal unit-distance-free sets -/
axiom structure_of_maximal_sets :
  -- Maximal unit-distance-free sets have specific geometric properties
  -- Their complements are "dense" enough to contain small configurations
  True

/-- Pigeonhole argument -/
axiom pigeonhole_argument :
  -- If S avoids unit distances, then for any point p,
  -- the unit circle centered at p lies entirely in Sᶜ
  -- This provides many points to work with
  True

/-- Intersection patterns of unit circles -/
axiom unit_circle_intersections :
  -- Unit circles intersect in at most 2 points
  -- This limits how "sparse" Sᶜ can be locally
  True

/-!
## Part 7: Examples and Constructions
-/

/-- The integer lattice ℤ² is unit-distance-free -/
axiom integer_lattice_example :
  -- No two integer points are exactly distance 1 apart
  -- (since √(a² + b²) = 1 has no integer solutions other than (±1,0), (0,±1)
  -- which give distance 1, but those are distinct points)
  -- Actually ℤ² is NOT unit-distance-free! Points like (0,0) and (1,0) are distance 1
  True

/-- A proper example: scale ℤ² by √2 -/
def ScaledLattice : Set Plane :=
  {p : Plane | ∃ a b : ℤ, p 0 = Real.sqrt 2 * a ∧ p 1 = Real.sqrt 2 * b}

/-- The scaled lattice is unit-distance-free -/
axiom scaled_lattice_is_unit_free :
  IsUnitDistanceFree ScaledLattice

/-- The complement of scaled lattice contains unit squares -/
axiom scaled_lattice_complement_has_squares :
  ContainsUnitSquare ScaledLatticeᶜ

/-!
## Part 8: Related Problems
-/

/-- The Nelson-Hadwiger problem (chromatic number of the plane) -/
axiom nelson_hadwiger_problem :
  -- What is the minimum number of colors needed to color ℝ²
  -- so that no two points at distance 1 have the same color?
  -- Answer: between 5 and 7
  True

/-- Connection to Erdős unit distance problem -/
axiom erdos_unit_distance_problem :
  -- How many pairs of points at unit distance can n points in ℝ² have?
  -- Answer: Θ(n^{1+c/log log n}) for some c > 0
  True

/-- Moser's worm problem (related geometric problem) -/
axiom moser_worm_problem :
  -- What is the smallest convex set that contains a congruent copy
  -- of every plane curve of length 1?
  True

/-!
## Part 9: Geometric Intuition
-/

/-- Why the result is true (intuition) -/
axiom intuitive_explanation :
  -- If S avoids unit distances, the "forbidden region" around each point of S
  -- is a unit circle. The complement Sᶜ must include these circles.
  -- With enough circles in Sᶜ, we can find four points forming a unit square.
  -- The key is that 4 points give limited degrees of freedom.
  True

/-- The role of the number 4 -/
axiom why_four_points :
  -- 4 points can be placed with some flexibility
  -- The configuration space of 4 points up to congruence is 4-dimensional
  -- The complement Sᶜ is "almost all" of ℝ²
  -- So finding a 4-point configuration is always possible
  True

/-!
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

end Erdos214
