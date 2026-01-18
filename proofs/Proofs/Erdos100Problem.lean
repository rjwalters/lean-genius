/-
Erdős Problem #100: Point Sets with Restricted Distances

Let A be a set of n points in ℝ² such that:
1. All pairwise distances are at least 1
2. Any two distinct distances differ by at least 1

**Question**: Is the diameter of A ≫ n?

**Status**: OPEN

**Known Results**:
- Piepmeyer: 9 points exist with diameter < 5
- Kanold: diameter ≥ n^(3/4)
- Guth-Katz (2015): implies diameter ≫ n/log n

**Conjecture**: Diameter may be ≥ n-1 for large n.

Reference: https://erdosproblems.com/100
Related: Erdős #89 (distinct distances problem)
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Set Finset

namespace Erdos100

/-!
## The Plane and Distance

We work in ℝ² with the standard Euclidean distance.
-/

/-- A point in the Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The Euclidean distance between two points. -/
noncomputable def dist (p q : Point) : ℝ := ‖p - q‖

/-!
## Restricted Distance Sets

A point set has restricted distances if:
1. All pairwise distances are ≥ 1
2. Any two distinct distances differ by ≥ 1

This means the distance multiset takes values in {1, 2, 3, ...} (positive integers).
-/

/-- All pairwise distances in a point set are at least 1. -/
def minDistanceOne (A : Finset Point) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, p ≠ q → dist p q ≥ 1

/-- Any two distinct distances in the set differ by at least 1.
    Equivalently: all distances are integers ≥ 1. -/
def integerDistances (A : Finset Point) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, p ≠ q → ∃ k : ℕ, k ≥ 1 ∧ dist p q = k

/-- A point set has restricted distances if it satisfies both conditions. -/
def hasRestrictedDistances (A : Finset Point) : Prop :=
  minDistanceOne A ∧ integerDistances A

/-!
## Diameter

The diameter of a point set is the maximum pairwise distance.
-/

/-- The diameter of a finite point set. -/
noncomputable def diameter (A : Finset Point) : ℝ :=
  if h : A.Nonempty then
    (A.sup' h fun p => A.sup' h fun q => dist p q)
  else 0

/-- Alternative: diameter as the supremum of all pairwise distances. -/
noncomputable def diameter' (A : Finset Point) : ℝ :=
  sSup { d : ℝ | ∃ p ∈ A, ∃ q ∈ A, d = dist p q }

/-!
## The Main Conjecture

Erdős asks whether the diameter must grow linearly with n.
-/

/-- The main conjecture: for restricted distance sets, diameter ≫ n.
    There exists c > 0 such that diameter(A) ≥ c · n for all A with |A| = n. -/
def erdos_100_conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ (A : Finset Point), hasRestrictedDistances A →
    diameter A ≥ c * A.card

/-- Stronger conjecture: diameter ≥ n - 1 for large n. -/
def erdos_100_strong_conjecture : Prop :=
  ∃ N : ℕ, ∀ (A : Finset Point), hasRestrictedDistances A →
    A.card ≥ N → diameter A ≥ A.card - 1

/-!
## Known Lower Bounds

Several lower bounds on the diameter have been established.
-/

/-- Kanold's bound: diameter ≥ n^(3/4). -/
axiom kanold_bound :
    ∀ (A : Finset Point), hasRestrictedDistances A →
    diameter A ≥ (A.card : ℝ) ^ (3/4 : ℝ)

/-- Guth-Katz bound: diameter ≥ c · n / log n for some constant c > 0.
    This follows from their solution to the distinct distances problem. -/
axiom guth_katz_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ (A : Finset Point), hasRestrictedDistances A →
    A.card ≥ 2 → diameter A ≥ c * A.card / log (A.card : ℝ)

/-!
## Known Upper Bounds (Constructions)

Piepmeyer showed the conjecture cannot be too strong.
-/

/-- Piepmeyer's construction: 9 points with restricted distances
    and diameter less than 5.

    This shows diameter(A) ≥ (n-1) fails for n = 9. -/
axiom piepmeyer_construction :
    ∃ (A : Finset Point), A.card = 9 ∧ hasRestrictedDistances A ∧ diameter A < 5

/-- Piepmeyer's example shows diameter / n can be less than 5/9 ≈ 0.56. -/
theorem piepmeyer_ratio :
    ∃ (A : Finset Point), hasRestrictedDistances A ∧
    diameter A / A.card < 5 / 9 := by
  obtain ⟨A, hcard, hrestr, hdiam⟩ := piepmeyer_construction
  use A
  constructor
  · exact hrestr
  · simp [hcard]
    linarith

/-!
## Connection to Distinct Distances Problem

This problem is related to Erdős #89 on distinct distances.
-/

/-- The number of distinct distances in a point set. -/
def numDistinctDistances (A : Finset Point) : ℕ :=
  ((A ×ˢ A).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)
    |>.card

/-- For restricted distance sets, distinct distances ≤ diameter.
    (Since distances are integers from 1 to diameter.) -/
theorem distinct_distances_le_diameter (A : Finset Point)
    (h : hasRestrictedDistances A) :
    numDistinctDistances A ≤ Nat.floor (diameter A) := by
  sorry

/-- Guth-Katz (2015): Any n points determine ≫ n / log n distinct distances.
    Combined with the above, this gives a lower bound on diameter. -/
axiom guth_katz_distinct_distances :
    ∃ c : ℝ, c > 0 ∧ ∀ (A : Finset Point), A.card ≥ 2 →
    (numDistinctDistances A : ℝ) ≥ c * A.card / log (A.card : ℝ)

/-!
## Trivial Bounds

We can establish some basic bounds.
-/

/-- Lower bound: diameter ≥ 1 for any set with ≥ 2 points and min distance 1. -/
theorem diameter_ge_one (A : Finset Point) (hA : A.card ≥ 2)
    (h : minDistanceOne A) : diameter A ≥ 1 := by
  sorry

/-- The diameter is achieved by some pair of points. -/
theorem diameter_achieved (A : Finset Point) (hA : A.Nonempty) :
    ∃ p ∈ A, ∃ q ∈ A, dist p q = diameter A := by
  sorry

/-!
## Unit Distance Graphs

The structure relates to unit distance graphs.
-/

/-- The unit distance graph: edges between points at distance exactly 1. -/
def unitDistanceGraph (A : Finset Point) : SimpleGraph Point where
  Adj p q := p ∈ A ∧ q ∈ A ∧ dist p q = 1
  symm := by
    intro p q ⟨hp, hq, hdist⟩
    refine ⟨hq, hp, ?_⟩
    simp only [dist] at hdist ⊢
    rw [norm_sub_rev]
    exact hdist
  loopless := by
    intro p ⟨_, _, hdist⟩
    simp [dist] at hdist

/-- For restricted distance sets, the unit distance graph captures
    all pairs at minimum distance. -/
theorem unit_graph_min_distance (A : Finset Point)
    (h : hasRestrictedDistances A) (p q : Point) (hp : p ∈ A) (hq : q ∈ A)
    (hpq : p ≠ q) : dist p q = 1 ↔ (unitDistanceGraph A).Adj p q := by
  sorry

/-!
## Lattice Point Configurations

One natural class of examples comes from lattice points.
-/

/-- The set of lattice points in a box. -/
def latticeBox (n : ℕ) : Finset Point :=
  sorry  -- Would need to construct explicitly

/-- Lattice points at integer coordinates have integer distances (when they exist). -/
theorem lattice_integer_distances :
    ∀ p q : Point, (∀ i, ∃ k : ℤ, p i = k) → (∀ i, ∃ k : ℤ, q i = k) →
    ∃ k : ℕ, dist p q = Real.sqrt k := by
  sorry

/-!
## Summary

This file formalizes Erdős Problem #100 on point sets with restricted distances.

**Status**: OPEN

**The Question**: For n points in ℝ² with pairwise distances ≥ 1 and
all distances differing by ≥ 1, must the diameter be ≫ n?

**Known Bounds**:
- Lower: n^(3/4) (Kanold), n/log n (Guth-Katz)
- Upper: 9 points with diameter < 5 (Piepmeyer)

**Key sorries**:
- `distinct_distances_le_diameter`: Count bound
- `diameter_ge_one`: Basic lower bound
- `diameter_achieved`: Diameter is realized
- `unit_graph_min_distance`: Unit graph characterization

**Connections**:
- Related to Erdős #89 (distinct distances problem)
- Guth-Katz solution to distinct distances gives the n/log n bound
-/

end Erdos100
