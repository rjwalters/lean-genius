/-
  Aristotle targets for Erdos660 (Distinct Distances in Convex Polyhedra)
  Routine supporting lemmas for automated proof search.
  See Erdos660Problem.lean for the main formalization.

  These lemmas provide building blocks for the distinct distances problem:
  - Basic distance properties (positivity, symmetry)
  - Finset membership and cardinality helpers
  - Structural properties of pairwiseDistances
  - Trivial lower bound proof
  - Specific geometric constructions (tetrahedron, cube, octahedron)
-/
import Mathlib

namespace Erdos660.Aristotle

open Finset Set

abbrev Point3D := EuclideanSpace ℝ (Fin 3)

/-
  ## Section 1: Basic Distance Lemmas
-/

/-- Distinct points in EuclideanSpace have positive distance -/
lemma dist_pos_of_ne (p q : Point3D) (h : p ≠ q) : 0 < dist p q := by
  sorry

/-- Distance is symmetric -/
lemma dist_comm' (p q : Point3D) : dist p q = dist q p := by
  sorry

/-- A Finset with card ≥ 2 has two distinct elements -/
lemma has_two_elements (S : Finset Point3D) (h : S.card ≥ 2) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q := by
  sorry

/-
  ## Section 2: pairwiseDistances Properties
-/

noncomputable def pairwiseDistances (S : Finset Point3D) : Finset ℝ :=
  (S.product S).image (fun pq => dist pq.1 pq.2)

noncomputable def distinctDistances (S : Finset Point3D) : ℕ :=
  ((pairwiseDistances S).filter (· > 0)).card

/-- A positive pairwise distance belongs to pairwiseDistances -/
lemma mem_pairwiseDistances (S : Finset Point3D) (p q : Point3D)
    (hp : p ∈ S) (hq : q ∈ S) : dist p q ∈ pairwiseDistances S := by
  sorry

/-- If p ≠ q and both are in S, dist p q > 0 and in pairwiseDistances S -/
lemma pos_dist_mem_filter (S : Finset Point3D) (p q : Point3D)
    (hp : p ∈ S) (hq : q ∈ S) (hne : p ≠ q) :
    dist p q ∈ (pairwiseDistances S).filter (· > 0) := by
  sorry

/-
  ## Section 3: Trivial Lower Bound
-/

/-- Any configuration with ≥ 2 points has ≥ 1 distinct positive distance -/
theorem trivial_lower_bound (S : Finset Point3D) (hn : S.card ≥ 2) :
    distinctDistances S ≥ 1 := by
  sorry

/-
  ## Section 4: Small Constructions
-/

/-- A two-point set has exactly 1 distinct distance -/
lemma two_point_one_distance (p q : Point3D) (hne : p ≠ q) :
    distinctDistances {p, q} = 1 := by
  sorry

/-- Pairwise distances of an empty set is empty -/
lemma pairwiseDistances_empty : pairwiseDistances (∅ : Finset Point3D) = ∅ := by
  sorry

/-- Pairwise distances of a singleton contains only 0 -/
lemma pairwiseDistances_singleton (p : Point3D) :
    pairwiseDistances {p} = {0} := by
  sorry

/-- A singleton has 0 distinct distances -/
lemma distinctDistances_singleton (p : Point3D) :
    distinctDistances {p} = 0 := by
  sorry

end Erdos660.Aristotle
