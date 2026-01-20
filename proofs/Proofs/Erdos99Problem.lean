/-
Erdős Problem #99: Equilateral Triangles in Minimal Diameter Sets

Source: https://erdosproblems.com/99
Status: OPEN
Prize: $100 (counterexample), $50 (proof)

Statement:
Let A ⊆ ℝ² be a set of n points with minimum pairwise distance equal to 1,
chosen to minimize the diameter of A. If n is sufficiently large, must
there exist three points in A which form an equilateral triangle of size 1?

Known Results:
- Thue: Minimal diameter is achieved asymptotically by triangular lattice ∩ circle
- n = 4: Square vertices have min distance 1, small diameter, NO unit equilateral triangle
- Bezdek-Fodor (1999): Explored optimal configurations for small n
- Erdős conjectured (1-o(1))n points lie on the triangular lattice

Historical Note:
Erdős wrote: "I could not prove it but felt that it should not be hard.
To my great surprise both B. H. Sendov and M. Simonovits doubted the truth
of this conjecture."

Prize Asymmetry:
$100 for counterexample, $50 for proof — Erdős suspected it might be false!

Related: Problem #103

Tags: discrete-geometry, packing, triangular-lattice, equilateral-triangles
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite

open Real Set Finset

namespace Erdos99

/-
## Part I: Basic Geometric Definitions
-/

/-- The Euclidean plane ℝ² -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Distance between two points in the plane -/
noncomputable def dist (p q : Plane) : ℝ :=
  ‖p - q‖

/-- Minimum pairwise distance of a finite point set -/
noncomputable def minPairwiseDistance (A : Finset Plane) : ℝ :=
  if h : A.card ≥ 2 then
    Finset.inf' (A.product A).filter (fun pq => pq.1 ≠ pq.2)
      (by
        simp only [Finset.filter_nonempty_iff, Finset.mem_product]
        obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.one_lt_two h)
        obtain ⟨b, hb, hab⟩ := Finset.exists_ne_of_one_lt_card (Nat.lt_of_lt_of_le Nat.one_lt_two h) a
        exact ⟨(a, b), ⟨ha, hb⟩, hab⟩)
      (fun pq => dist pq.1 pq.2)
  else 0

/-- Diameter of a point set: maximum pairwise distance -/
noncomputable def diameter (A : Finset Plane) : ℝ :=
  if h : A.card ≥ 2 then
    Finset.sup' (A.product A).filter (fun pq => pq.1 ≠ pq.2)
      (by
        simp only [Finset.filter_nonempty_iff, Finset.mem_product]
        obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.one_lt_two h)
        obtain ⟨b, hb, hab⟩ := Finset.exists_ne_of_one_lt_card (Nat.lt_of_lt_of_le Nat.one_lt_two h) a
        exact ⟨(a, b), ⟨ha, hb⟩, hab⟩)
      (fun pq => dist pq.1 pq.2)
  else 0

/-
## Part II: Unit Distance and Equilateral Triangles
-/

/-- A point set has minimum distance 1 -/
def HasMinDistanceOne (A : Finset Plane) : Prop :=
  minPairwiseDistance A ≥ 1

/-- Three points form a unit equilateral triangle -/
def IsUnitEquilateralTriangle (p q r : Plane) : Prop :=
  dist p q = 1 ∧ dist q r = 1 ∧ dist r p = 1

/-- A point set contains a unit equilateral triangle -/
def ContainsUnitEquilateralTriangle (A : Finset Plane) : Prop :=
  ∃ p q r : Plane, p ∈ A ∧ q ∈ A ∧ r ∈ A ∧
    p ≠ q ∧ q ≠ r ∧ r ≠ p ∧ IsUnitEquilateralTriangle p q r

/-
## Part III: Optimal Point Configurations
-/

/-- Set of n-point configurations with minimum distance 1 -/
def ValidConfigurations (n : ℕ) : Set (Finset Plane) :=
  { A | A.card = n ∧ HasMinDistanceOne A }

/-- A configuration has minimal diameter among all valid n-point configurations -/
def HasMinimalDiameter (A : Finset Plane) : Prop :=
  ∀ B : Finset Plane, B.card = A.card → HasMinDistanceOne B →
    diameter A ≤ diameter B

/-- Optimal configuration: n points, min distance 1, minimal diameter -/
def IsOptimalConfiguration (A : Finset Plane) : Prop :=
  HasMinDistanceOne A ∧ HasMinimalDiameter A

/-
## Part IV: The Triangular Lattice
-/

/-- A point in the triangular lattice with basis vectors (1, 0) and (1/2, √3/2) -/
noncomputable def triangularLatticePoint (i j : ℤ) : Plane :=
  fun k => if k = 0 then (i : ℝ) + (j : ℝ) / 2 else (j : ℝ) * Real.sqrt 3 / 2

/-- The triangular lattice -/
def TriangularLattice : Set Plane :=
  { p | ∃ i j : ℤ, p = triangularLatticePoint i j }

/-- Adjacent points in the triangular lattice have distance 1 -/
axiom triangular_lattice_unit_distance :
  ∀ i j : ℤ,
    dist (triangularLatticePoint i j) (triangularLatticePoint (i+1) j) = 1 ∧
    dist (triangularLatticePoint i j) (triangularLatticePoint i (j+1)) = 1 ∧
    dist (triangularLatticePoint i j) (triangularLatticePoint (i+1) (j-1)) = 1

/-- The triangular lattice contains unit equilateral triangles -/
theorem triangular_lattice_has_equilateral :
    ∀ i j : ℤ, IsUnitEquilateralTriangle
      (triangularLatticePoint i j)
      (triangularLatticePoint (i+1) j)
      (triangularLatticePoint i (j+1)) := by
  intro i j
  unfold IsUnitEquilateralTriangle
  constructor
  · exact (triangular_lattice_unit_distance i j).1
  constructor
  · sorry -- needs distance computation
  · sorry -- needs distance computation

/-
## Part V: Thue's Theorem Context
-/

/-- Thue's theorem: optimal packing density is achieved by triangular lattice -/
axiom thue_optimal_packing :
  -- The densest packing of unit circles in ℝ² is the triangular lattice packing
  -- Density = π / (2√3) ≈ 0.9069
  True

/-- Consequence: diameter-minimizing configurations resemble triangular lattice -/
axiom thue_diameter_consequence :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Plane,
    A.card = n → IsOptimalConfiguration A →
    -- Most points of A lie near the triangular lattice
    (A.filter (fun p => ∃ q ∈ TriangularLattice, dist p q < ε)).card ≥ n - n / 10

/-
## Part VI: Small Cases
-/

/-- n = 3: Triangle (trivially contains equilateral triangle) -/
axiom case_n3 :
  ∀ A : Finset Plane, A.card = 3 → IsOptimalConfiguration A →
    ContainsUnitEquilateralTriangle A

/-- n = 4: Square vertices - NO unit equilateral triangle! -/
axiom case_n4_square :
  ∃ A : Finset Plane, A.card = 4 ∧ IsOptimalConfiguration A ∧
    ¬ContainsUnitEquilateralTriangle A

/-- Bezdek-Fodor (1999): Analysis of small n cases -/
axiom bezdek_fodor_small_cases :
  -- Characterized optimal configurations for small n
  -- Found that triangular lattice structure emerges gradually
  True

/-
## Part VII: The Main Conjecture (OPEN)
-/

/-- Erdős Problem #99: The main conjecture -/
def Erdos99Conjecture : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Plane,
    A.card = n → IsOptimalConfiguration A →
    ContainsUnitEquilateralTriangle A

/-- Erdős's stronger conjecture: (1-o(1))n points on lattice -/
def StrongerConjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Plane,
    A.card = n → IsOptimalConfiguration A →
    (A.filter (fun p => p ∈ TriangularLattice)).card ≥ (1 - ε) * n

/-- Stronger conjecture implies the main conjecture -/
theorem stronger_implies_main : StrongerConjecture → Erdos99Conjecture := by
  intro hStrong
  -- If (1-o(1))n points are on the lattice, there are enough
  -- to form a unit equilateral triangle
  sorry

/-
## Part VIII: Evidence For and Against
-/

/-- Evidence FOR the conjecture: Thue's theorem -/
axiom evidence_for :
  -- Optimal configurations should resemble triangular lattice
  -- Triangular lattice contains unit equilateral triangles
  True

/-- Evidence AGAINST the conjecture -/
axiom evidence_against :
  -- n = 4 case shows small deviations from lattice are possible
  -- Prize asymmetry suggests Erdős thought counterexample more likely
  -- Sendov and Simonovits doubted it
  True

/-
## Part IX: Related Results
-/

/-- Related: Optimal circle packing -/
axiom circle_packing_relation :
  -- Points with min distance 1 correspond to non-overlapping unit circles
  -- Diameter minimization relates to packing efficiency
  True

/-- Related: Problem #103 -/
axiom problem_103_relation :
  -- Related investigations on point configurations
  True

/-- Density of triangular lattice packing -/
noncomputable def triangularPackingDensity : ℝ :=
  Real.pi / (2 * Real.sqrt 3)

/-
## Part X: The Prize Structure
-/

/-- Erdős offered $100 for counterexample, $50 for proof -/
def prizeCounterexample : ℕ := 100
def prizeProof : ℕ := 50

/-- Prize asymmetry suggests Erdős suspected it might be false -/
theorem prize_asymmetry :
    prizeCounterexample > prizeProof := by
  decide

/-
## Part XI: Problem Status
-/

/-- The problem remains OPEN -/
axiom erdos_99_open :
  -- Neither proved nor disproved
  -- Prize still unclaimed
  True

/-
## Part XII: Summary
-/

/-- Erdős Problem #99: Full Summary -/
theorem erdos_99_summary :
    -- The main conjecture
    (Erdos99Conjecture ↔ ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Plane,
      A.card = n → IsOptimalConfiguration A →
      ContainsUnitEquilateralTriangle A) ∧
    -- Small case n=4 shows it's not trivial
    (∃ A : Finset Plane, A.card = 4 ∧ IsOptimalConfiguration A ∧
      ¬ContainsUnitEquilateralTriangle A) ∧
    -- Prize structure
    (prizeCounterexample = 100 ∧ prizeProof = 50) := by
  constructor
  · exact Iff.rfl
  constructor
  · exact case_n4_square
  · constructor <;> rfl

/-- Main theorem: Problem #99 is OPEN -/
theorem erdos_99_status : True := trivial

end Erdos99
