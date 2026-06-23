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

References: [Er94b], [Er95], [Er97e]
Related: Problem #103
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite

open Real Set Finset

namespace Erdos99

/- ## Part I: Basic Geometric Definitions -/

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

/- ## Part II: Unit Distance and Equilateral Triangles -/

/-- A point set has minimum distance at least 1 -/
def HasMinDistanceOne (A : Finset Plane) : Prop :=
  minPairwiseDistance A ≥ 1

/-- Three points form a unit equilateral triangle -/
def IsUnitEquilateralTriangle (p q r : Plane) : Prop :=
  dist p q = 1 ∧ dist q r = 1 ∧ dist r p = 1

/-- A point set contains a unit equilateral triangle -/
def ContainsUnitEquilateralTriangle (A : Finset Plane) : Prop :=
  ∃ p q r : Plane, p ∈ A ∧ q ∈ A ∧ r ∈ A ∧
    p ≠ q ∧ q ≠ r ∧ r ≠ p ∧ IsUnitEquilateralTriangle p q r

/- ## Part III: Optimal Point Configurations -/

/-- A configuration has minimal diameter among all valid n-point configurations -/
def HasMinimalDiameter (A : Finset Plane) : Prop :=
  ∀ B : Finset Plane, B.card = A.card → HasMinDistanceOne B →
    diameter A ≤ diameter B

/-- Optimal configuration: n points, min distance 1, minimal diameter -/
def IsOptimalConfiguration (A : Finset Plane) : Prop :=
  HasMinDistanceOne A ∧ HasMinimalDiameter A

/- ## Part IV: The Triangular Lattice -/

/-- A point in the triangular lattice with basis vectors (1, 0) and (1/2, √3/2) -/
noncomputable def triangularLatticePoint (i j : ℤ) : Plane :=
  fun k => if k = 0 then (i : ℝ) + (j : ℝ) / 2 else (j : ℝ) * Real.sqrt 3 / 2

/-- The triangular lattice -/
def TriangularLattice : Set Plane :=
  { p | ∃ i j : ℤ, p = triangularLatticePoint i j }

/--
Adjacent points in the triangular lattice have distance 1. This captures
the three lattice directions: horizontal, 60°, and 120°.
-/
/--
Any three adjacent lattice points form a unit equilateral triangle.
This is why the conjecture seems plausible: if optimal configurations
resemble the lattice, they should contain such triangles.
-/
/- ## Part V: Thue's Theorem and Lattice Structure -/

/--
Thue's theorem implies that diameter-minimizing configurations
asymptotically resemble regions of the triangular lattice. For any ε > 0,
in a large enough optimal configuration, at least (1 - ε)n points lie
within distance ε of some triangular lattice point.
-/
/- ## Part VI: Small Cases -/

/-- n = 3: An optimal 3-point set must be an equilateral triangle -/
/--
n = 4: The square with unit side length is an optimal 4-point configuration
that does NOT contain a unit equilateral triangle. This shows the conjecture
fails for small n and is the key evidence suggesting a counterexample might exist.
-/
axiom case_n4_no_equilateral :
  ∃ A : Finset Plane, A.card = 4 ∧ IsOptimalConfiguration A ∧
    ¬ContainsUnitEquilateralTriangle A

/- ## Part VII: The Main Conjecture (OPEN) -/

/--
**Erdős Problem #99:** For sufficiently large n, every optimal n-point
configuration (minimum distance 1, minimal diameter) must contain a
unit equilateral triangle.
-/
def Erdos99Conjecture : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Plane,
    A.card = n → IsOptimalConfiguration A →
    ContainsUnitEquilateralTriangle A

/--
Erdős's stronger conjecture: in any optimal configuration of n points,
(1-o(1))n of them lie exactly on the triangular lattice.
-/
def StrongerConjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Plane,
    A.card = n → IsOptimalConfiguration A →
    (A.filter (fun p => p ∈ TriangularLattice)).card ≥ (1 - ε) * n

/--
The density of the triangular lattice packing: π/(2√3) ≈ 0.9069.
This is the maximum packing density for unit circles in ℝ² (Thue's theorem).
-/
noncomputable def triangularPackingDensity : ℝ :=
  Real.pi / (2 * Real.sqrt 3)

/- ## Part VIII: Summary -/

/--
**Erdős Problem #99: Summary**

The n=4 square case shows that optimal configurations can avoid unit
equilateral triangles for small n. The conjecture asks whether this is
impossible for sufficiently large n.
-/
theorem erdos_99_summary :
    (∃ A : Finset Plane, A.card = 4 ∧ IsOptimalConfiguration A ∧
      ¬ContainsUnitEquilateralTriangle A) :=
  case_n4_no_equilateral

end Erdos99
