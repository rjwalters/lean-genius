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

/-- Juhász's Theorem (1979): Affirmatively resolves Problem #214 -/
axiom juhasz_1979 : Erdos214Statement

/-- The main theorem: Problem #214 is solved -/
theorem erdos_214_solved : Erdos214Statement := juhasz_1979

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

/-- Unit square is a special case of 4-point configurations -/
theorem unit_square_from_stronger :
    JuhaszStrongerTheorem → Erdos214Statement := by
  intro hStrong S hFree
  -- A unit square is a particular 4-point configuration
  -- Apply Juhász's stronger theorem
  sorry

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

/-
## Part 6: Proof Techniques
-/

/-
## Part 7: Examples and Constructions
-/

/-- A proper example: scale ℤ² by √2 -/
def ScaledLattice : Set Plane :=
  {p : Plane | ∃ a b : ℤ, p 0 = Real.sqrt 2 * a ∧ p 1 = Real.sqrt 2 * b}

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

end Erdos214
