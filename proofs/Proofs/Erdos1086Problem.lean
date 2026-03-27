/-
Erdős Problem #1086: Triangles of Equal Area

Source: https://erdosproblems.com/1086
Status: OPEN

Statement:
Let g(n) be minimal such that any set of n points in ℝ² contains the vertices
of at most g(n) many triangles with the same area. Estimate g(n).

Equivalently: How many triangles of area 1 can a set of n points in ℝ² determine?

Known Bounds:
- Lower: n² log log n ≪ g(n) (Erdős-Purdy 1971)
- Upper: g(n) ≪ n^{20/9} (Raz-Sharir 2017)

History:
- Oppenheim posed the original question
- Erdős-Purdy (1971): n² log log n ≪ g(n) ≪ n^{5/2}
- Pach-Sharir (1992): improved upper bound
- Dumitrescu-Sharir-Tóth (2009): further improvements
- Apfelbaum-Sharir (2010): continued improvements
- Raz-Sharir (2017): g(n) ≪ n^{20/9} (current best)

Tags: geometry, combinatorics, incidence-geometry
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos1086

open Real

/- ## Part 1: Basic Definitions

Points in ℝ² and triangle area.
-/

/-- A point in the Euclidean plane -/
abbrev Point2D := EuclideanSpace ℝ (Fin 2)

/-- Extract x-coordinate -/
def Point2D.x (p : Point2D) : ℝ := p 0

/-- Extract y-coordinate -/
def Point2D.y (p : Point2D) : ℝ := p 1

/-- Area of a triangle with vertices A, B, C using the shoelace formula
    Area = ½|x_A(y_B - y_C) + x_B(y_C - y_A) + x_C(y_A - y_B)| -/
noncomputable def triangleArea (A B C : Point2D) : ℝ :=
  |A.x * (B.y - C.y) + B.x * (C.y - A.y) + C.x * (A.y - B.y)| / 2

/-- A triple of distinct points -/
structure Triangle where
  A : Point2D
  B : Point2D
  C : Point2D
  distinct_AB : A ≠ B
  distinct_BC : B ≠ C
  distinct_CA : C ≠ A

/-- Area of a Triangle structure -/
noncomputable def Triangle.area (t : Triangle) : ℝ :=
  triangleArea t.A t.B t.C

/- ## Part 2: The Function g(n)

g(n) = maximum number of triangles of the same area formable from n points.
-/

/-- Given a set of points, count triangles with a specific area -/
noncomputable def countTrianglesWithArea (S : Finset Point2D) (α : ℝ) : ℕ :=
  -- Count unordered triples {A, B, C} ⊆ S with area α
  (S.powersetCard 3).filter (fun T =>
    ∃ (A B C : Point2D), A ∈ T ∧ B ∈ T ∧ C ∈ T ∧ A ≠ B ∧ B ≠ C ∧ C ≠ A ∧
      triangleArea A B C = α) |>.card

/-- Maximum count of triangles with the same area, over all areas -/
noncomputable def maxTrianglesWithSameArea (S : Finset Point2D) : ℕ :=
  -- Maximum over all possible areas
  sSup { countTrianglesWithArea S α | α : ℝ }

/-- The function g(n): max over all n-point sets of maxTrianglesWithSameArea -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup { maxTrianglesWithSameArea S | S : Finset Point2D // S.card = n }

/- ## Part 3: Known Bounds
-/

/-- Lower bound: n² log log n ≪ g(n) -/
axiom lower_bound_erdos_purdy (n : ℕ) (hn : n ≥ 16) :
  ∃ C > 0, g n ≥ C * n^2 * Real.log (Real.log n)

/-- Improved upper bound by Raz-Sharir (2017): g(n) ≪ n^{20/9} -/
axiom upper_bound_raz_sharir_2017 (n : ℕ) (hn : n ≥ 2) :
  ∃ C > 0, g n ≤ C * n^(20/9 : ℝ)

/-- The exponent 20/9 ≈ 2.222 is the current best upper bound -/
def bestUpperExponent : ℝ := 20 / 9

/- ## Part 4: Higher-Dimensional Generalizations

Let g_d^r(n) = max simplices of same volume from n points in ℝ^d.
-/

/-- Generalized function for d-dimensional space, r-simplices.
    g_dim d r n is the maximum number of r-simplices of the same volume
    determined by n points in ℝ^d. Axiomatized since the definition involves
    a supremum over all point configurations in ℝ^d. -/
axiom g_dim (d r : ℕ) (n : ℕ) : ℕ

/-- Dumitrescu-Sharir-Tóth (2009): g_3^2(n) ≪ n^{2.4286} -/
axiom bound_g3_2_dst (n : ℕ) (hn : n ≥ 2) :
  ∃ C > 0, g_dim 3 2 n ≤ C * n^(2.4286 : ℝ)

/- ## Part 5: Simple Examples
-/

/- ## Part 6: Connection to Incidence Geometry
-/

/- ## Part 7: Main Results
-/

/-- Erdős Problem #1086: Main statement combining lower and upper bounds -/
theorem erdos_1086_statement (n : ℕ) (hn : n ≥ 16) :
    -- Lower bound: n² log log n ≪ g(n)
    (∃ C > 0, g n ≥ C * n^2 * Real.log (Real.log n)) ∧
    -- Upper bound: g(n) ≪ n^{20/9}
    (∃ C > 0, g n ≤ C * n^(20/9 : ℝ)) :=
  ⟨lower_bound_erdos_purdy n hn,
   upper_bound_raz_sharir_2017 n (by omega)⟩

/-- Summary: bounds on g(n) and higher-dimensional generalizations -/
theorem erdos_1086_summary (n : ℕ) (hn : n ≥ 16) :
    -- 1. Lower bound: n² log log n ≪ g(n) (Erdős-Purdy 1971)
    (∃ C > 0, g n ≥ C * n^2 * Real.log (Real.log n)) ∧
    -- 2. Upper bound: g(n) ≪ n^{20/9} (Raz-Sharir 2017)
    (∃ C > 0, g n ≤ C * n^(20/9 : ℝ)) ∧
    -- 3. In 3D: g_3^2(n) ≪ n^{2.4286}
    (∃ C > 0, g_dim 3 2 n ≤ C * n^(2.4286 : ℝ)) :=
  ⟨lower_bound_erdos_purdy n hn,
   upper_bound_raz_sharir_2017 n (by omega),
   bound_g3_2_dst n (by omega)⟩

end Erdos1086
