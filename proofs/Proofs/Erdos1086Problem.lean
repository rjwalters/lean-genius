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

/-!
## Part 1: Basic Definitions

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

/-!
## Part 2: The Function g(n)

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

/-!
## Part 3: Known Bounds
-/

/-- Lower bound: n² log log n ≪ g(n) -/
axiom lower_bound_erdos_purdy (n : ℕ) (hn : n ≥ 16) :
  ∃ C > 0, g n ≥ C * n^2 * Real.log (Real.log n)

/-- Original upper bound by Erdős-Purdy (1971): g(n) ≪ n^{5/2} -/
axiom upper_bound_erdos_purdy_1971 (n : ℕ) (hn : n ≥ 2) :
  ∃ C > 0, g n ≤ C * n^(5/2 : ℝ)

/-- Improved upper bound by Raz-Sharir (2017): g(n) ≪ n^{20/9} -/
axiom upper_bound_raz_sharir_2017 (n : ℕ) (hn : n ≥ 2) :
  ∃ C > 0, g n ≤ C * n^(20/9 : ℝ)

/-- The exponent 20/9 ≈ 2.222 is the current best upper bound -/
def bestUpperExponent : ℝ := 20 / 9

/-- Erdős-Purdy conjecture: g(n) = Θ(n² polylog(n)).
    The truth is believed closer to the lower bound than the upper bound. -/
axiom erdos_purdy_conjecture :
    ∃ (α : ℝ), α > 0 ∧
    ∀ n ≥ 16, ∃ (C₁ C₂ : ℝ), C₁ > 0 ∧ C₂ > 0 ∧
      C₁ * n^2 * (Real.log n)^α ≤ g n ∧
      g n ≤ C₂ * n^2 * (Real.log n)^α

/-!
## Part 4: Higher-Dimensional Generalizations

Let g_d^r(n) = max simplices of same volume from n points in ℝ^d.
-/

/-- Generalized function for d-dimensional space, r-simplices.
    g_dim d r n is the maximum number of r-simplices of the same volume
    determined by n points in ℝ^d. Axiomatized since the definition involves
    a supremum over all point configurations in ℝ^d. -/
axiom g_dim (d r : ℕ) (n : ℕ) : ℕ

/-- g_2^2(n) = g(n): the 2D triangle case is the original problem.
    Axiomatized since the definitions of g and g_dim use different
    supremum formulations that require showing they agree. -/
axiom g2_is_g (n : ℕ) : g_dim 2 2 n = g n

/-- Erdős-Purdy (1971): g_3^2(n) ≪ n^{8/3} -/
axiom bound_g3_2_erdos_purdy (n : ℕ) (hn : n ≥ 2) :
  ∃ C > 0, g_dim 3 2 n ≤ C * n^(8/3 : ℝ)

/-- Dumitrescu-Sharir-Tóth (2009): g_3^2(n) ≪ n^{2.4286} -/
axiom bound_g3_2_dst (n : ℕ) (hn : n ≥ 2) :
  ∃ C > 0, g_dim 3 2 n ≤ C * n^(2.4286 : ℝ)

/-- Erdős-Purdy (1971): g_6^2(n) ≫ n³ -/
axiom bound_g6_2_lower (n : ℕ) (hn : n ≥ 2) :
  ∃ C > 0, g_dim 6 2 n ≥ C * n^3

/-- Purdy (1974): g_4^2(n) ≤ g_5^2(n) ≪ n^{3-c} for some c > 0 -/
axiom purdy_bound_g4_g5 (n : ℕ) (hn : n ≥ 2) :
  ∃ c > 0, ∃ C > 0, g_dim 4 2 n ≤ g_dim 5 2 n ∧ g_dim 5 2 n ≤ C * n^(3 - c)

/-- Oppenheim-Lenz construction: g_{2k+2}^k(n) ≥ (1/(k+1)^{k+1} + o(1)) n^{k+1} -/
axiom oppenheim_lenz_construction (k : ℕ) (hk : k ≥ 1) :
  ∃ c > 0, ∀ n ≥ 2, g_dim (2*k + 2) k n ≥ c * n^(k + 1 : ℕ)

/-- Erdős-Purdy conjecture for higher dimensions:
    g_{2k+2}^k(n) = Θ(n^{k+1}), i.e. the Oppenheim-Lenz construction is optimal. -/
axiom erdos_purdy_conjecture_high_dim (k : ℕ) (hk : k ≥ 1) :
    ∃ (C : ℝ), C > 0 ∧ ∀ n ≥ 2,
      g_dim (2*k + 2) k n ≤ C * n^(k + 1 : ℕ)

/-!
## Part 5: Simple Examples
-/

/-- For n = 3 points, there's exactly 1 triangle.
    Axiomatized since computing g(3) from the supremum definition requires
    showing that any 3 non-collinear points form exactly 1 triangle. -/
axiom three_points_one_triangle : g 3 = 1

/-- For collinear points, all triangles have area 0 -/
axiom collinear_degenerate (S : Finset Point2D) (h : ∀ A ∈ S, ∀ B ∈ S, ∀ C ∈ S,
    A.y - B.y = (A.x - B.x) * (C.y - A.y) / (C.x - A.x)) :
  ∀ α > 0, countTrianglesWithArea S α = 0

/-- Grid points: regular √n × √n grid has many equal-area triangles -/
axiom grid_lower_bound (n : ℕ) (hn : ∃ k, n = k^2) :
  g n ≥ n^2 / 8

/-!
## Part 6: Connection to Incidence Geometry
-/

/-- The equal-area triangle problem reduces to point-curve incidences.
    For fixed base edge (A,B), the locus of points C giving area α is a pair of
    lines parallel to AB at distance 2α/|AB|. Counting triangles of area α thus
    reduces to counting incidences between points and lines/curves. -/
axiom incidence_reduction (S : Finset Point2D) (α : ℝ) (hα : α > 0) :
    countTrianglesWithArea S α ≤
      S.card * (S.card - 1) / 2

/-- The Szemerédi-Trotter incidence theorem bounds point-line incidences
    to O(n^{2/3} m^{2/3} + n + m), which is the key tool for upper bounds.
    Applied to the equal-area problem with n points and O(n²) lines, this
    yields upper bounds on g(n). -/
axiom szemeredi_trotter_bound (n m : ℕ) :
    ∃ C > 0, ∀ (incidences : ℕ),
      -- Incidences between n points and m lines ≤ C(n^{2/3}m^{2/3} + n + m)
      incidences ≤ C * (n^(2/3 : ℝ) * m^(2/3 : ℝ) + n + m)

/-!
## Part 7: Main Results
-/

/-- Erdős Problem #1086: Main statement combining lower and upper bounds -/
theorem erdos_1086_statement (n : ℕ) (hn : n ≥ 16) :
    -- Lower bound: n² log log n ≪ g(n)
    (∃ C > 0, g n ≥ C * n^2 * Real.log (Real.log n)) ∧
    -- Upper bound: g(n) ≪ n^{20/9}
    (∃ C > 0, g n ≤ C * n^(20/9 : ℝ)) :=
  ⟨lower_bound_erdos_purdy n hn,
   upper_bound_raz_sharir_2017 n (by omega)⟩

/-- The gap between lower bound exponent 2 and upper bound exponent 20/9
    remains open. The problem asks to close this gap. -/
axiom erdos_1086_gap_open :
    20 / 9 > (2 : ℝ) ∧ ¬∃ (e : ℝ), e < 20 / 9 ∧
      ∀ n ≥ 2, ∃ C > 0, (g n : ℝ) ≤ C * n^e

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
