/-
  Aristotle target (self-contained): Klein's upper bound for the Happy Ending
  Problem — the single remaining axiom of `Erdos107OQ01`.

  Goal: any five points in general position in the plane contain a convex
  quadrilateral.  All supporting definitions (`InGeneralPosition`,
  `IsConvexNGon`, `HasConvexNGon`, `CardSet`) are inlined here so the file is
  self-contained for automated proof search (no local-project imports).

  Classical proof (Klein 1931), by the size of the convex hull of the 5 points:
    • Hull has 4 or 5 vertices: any 4 hull vertices are in convex position.
    • Hull is a triangle: the remaining 2 points lie strictly inside.  The line
      through those 2 interior points misses all 3 triangle vertices (general
      position), so 2 of the 3 vertices lie on the same side; those 2 vertices
      with the 2 interior points form a convex quadrilateral.
-/
import Mathlib

namespace KleinUpperAristotle

open Finset

/-- A finite set of points is in **general position** if no three of its
    points are collinear. -/
def InGeneralPosition (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p q r : EuclideanSpace ℝ (Fin 2), p ∈ S → q ∈ S → r ∈ S →
    p ≠ q → q ≠ r → p ≠ r → ¬Collinear ℝ ({p, q, r} : Set _)

/-- `n` points form a **convex `n`-gon** if each is a vertex of the convex hull
    of the set, i.e. lies outside the hull of the others. -/
def IsConvexNGon (n : ℕ) (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  S.card = n ∧ ∀ p ∈ S, p ∉ convexHull ℝ ((S.erase p : Set _))

/-- A point set **contains a convex `n`-gon** if some `n`-point subset is one. -/
def HasConvexNGon (n : ℕ) (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ T ⊆ S, IsConvexNGon n T

/-- The set of `N` such that any `N` points in general position contain a
    convex `n`-gon. -/
def CardSet (n : ℕ) : Set ℕ :=
  { N | ∀ (pts : Finset (EuclideanSpace ℝ (Fin 2))),
    pts.card = N → InGeneralPosition ↑pts → HasConvexNGon n pts }

/-- **Klein 1931 (upper bound).** Any five points in general position in the
    plane contain a convex quadrilateral: `5 ∈ CardSet 4`. -/
theorem klein_upper_bound : (5 : ℕ) ∈ CardSet 4 := by
  sorry

end KleinUpperAristotle
