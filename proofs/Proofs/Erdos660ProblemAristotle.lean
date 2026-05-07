/-
  Aristotle targets for Erdős Problem #660: Distinct Distances in Convex Polyhedra
  Routine supporting lemmas for automated proof search.
  See Erdos660Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open problem (erdos_660_conjecture — OPEN)
  - NOT Altman's theorem (altman_convex_polygon_distances — deep 2D result)
  - NOT the weak conjectured linear bound (linear_lower_bound_conjecture — OPEN)
  - NOT Guth-Katz (guth_katz_distinct_distances — deep 2015 result)
  - Trivial metric lower bound: ≥2 distinct points → ≥1 positive distance
  - Symmetry: pairwiseDistances is symmetric in the two arguments
  - Monotonicity: adding a point can only increase or maintain distinctDistances
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings

  Included targets (3):
  - trivial_lower_bound_ari: S.card ≥ 2 → distinctDistances S ≥ 1
  - pairwiseDist_self_zero_ari: euclideanDist p p = 0 (metric reflexivity)
  - pairwiseDist_comm_ari: euclideanDist p q = euclideanDist q p (metric symmetry)
-/
import Proofs.Erdos660Problem
import Mathlib

namespace Erdos660Aristotle

open Erdos660 Finset Real

/-
## Section 1: Trivial Metric Lower Bound

If S has at least 2 points, they must be distinct, so dist p q > 0 for some p, q.
This gives at least one positive pairwise distance, hence distinctDistances S ≥ 1.
-/

/-- Any finite set of ≥2 points in ℝ³ determines at least 1 distinct (positive) distance.
Key steps: extract two distinct points, use dist_pos to get positivity, membership in image. -/
theorem trivial_lower_bound_ari
    (S : Finset Point3D)
    (hn : S.card ≥ 2) :
    distinctDistances S ≥ 1 := by
  sorry

/-
## Section 2: Zero Self-Distance

The Euclidean distance from any point to itself is 0.
This follows directly from the metric axiom dist_self.
-/

/-- The distance from any point to itself is 0. Follows from dist_self. -/
theorem pairwiseDist_self_zero_ari (p : Point3D) :
    euclideanDist p p = 0 := by
  sorry

/-
## Section 3: Metric Symmetry

The Euclidean distance satisfies dist p q = dist q p.
This follows from the metric axiom dist_comm.
-/

/-- The Euclidean distance is symmetric: euclideanDist p q = euclideanDist q p.
Follows directly from dist_comm. -/
theorem pairwiseDist_comm_ari (p q : Point3D) :
    euclideanDist p q = euclideanDist q p := by
  sorry

end Erdos660Aristotle
