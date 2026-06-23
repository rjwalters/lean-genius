/-
Erdős Problem #216: Empty Convex Polygons

Source: https://erdosproblems.com/216
Status: PARTIALLY SOLVED (g(k) resolved for all k)

Statement:
Let g(k) be the smallest integer (if it exists) such that any g(k) points in ℝ²
contains an empty convex k-gon (a convex k-gon with no point in its interior).
Does g(k) exist? If so, estimate g(k).

Answer:
- g(3) = 3 (trivial)
- g(4) = 5 (Erdős)
- g(5) = 10 (Harborth, 1978)
- g(6) = 30 (Heule-Scheucher, 2024)
- g(k) does NOT exist for k ≥ 7 (Horton, 1983)

Historical Notes:
This is a variant of the "Happy Ending Problem" (Erdős #107), which asks the same
without the empty interior condition. The happy ending problem has g'(k) = 2^(k-2) + 1
(Klein's observation, now a conjecture for k > 5).

Key Insight:
Horton sets provide point configurations with arbitrarily many points but no empty
7-gon. The existence of g(6) was a long-standing open problem, finally resolved
by computer-assisted proof (Heule-Scheucher 2024).

References:
- [Ha78] Harborth (1978), "Konvexe Fünfecke in ebenen Punktmengen"
- [Ho83] Horton (1983), "Sets with no empty convex 7-gons"
- [Ni07] Nicolás (2007), "The empty hexagon theorem"
- [Ge08] Gerken (2008), "Empty convex hexagons in planar point sets"
- [HeSc24] Heule-Scheucher (2024), "Happy Ending: An Empty Hexagon in Every Set of 30 Points"

Tags: discrete-geometry, convex-geometry, empty-polygons, ramsey-theory
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic

open Finset

namespace Erdos216

/-
## Part I: Basic Definitions
-/

/-- A point in the Euclidean plane -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A finite point set in the plane -/
def PointSet := Finset Point

/-- Points are in general position if no three are collinear.
Axiomatized since the full definition requires cross products. -/
axiom InGeneralPosition (S : PointSet) : Prop

/-- A subset forms a convex k-gon (k vertices in convex position).
Axiomatized since the full definition requires convex hull checks. -/
axiom IsConvexKGon (vertices : Finset Point) (k : ℕ) : Prop

/-
## Part II: Empty Convex Polygons
-/

/-- A convex k-gon is empty if no point of S lies strictly inside it.
Axiomatized since formalizing "interior of convex hull" requires
substantial geometric infrastructure. -/
axiom IsEmptyConvexKGon (S : PointSet) (vertices : Finset Point) (k : ℕ) : Prop

/-- S contains an empty convex k-gon -/
def ContainsEmptyKGon (S : PointSet) (k : ℕ) : Prop :=
  ∃ vertices : Finset Point, IsEmptyConvexKGon S vertices k

/-
## Part III: The Function g(k)
-/

/-- g(k) is the smallest n such that any n points in general position
    contain an empty convex k-gon -/
noncomputable def g (k : ℕ) : Option ℕ :=
  if h : ∃ n : ℕ, ∀ S : PointSet, S.card ≥ n → InGeneralPosition S → ContainsEmptyKGon S k
  then some (Nat.find h)
  else none

/-- g(k) exists means the function returns some value -/
def gExists (k : ℕ) : Prop := (g k).isSome

/-
## Part IV: Known Values
-/

/-- g(3) = 3: Any 3 points form an empty triangle (trivial) -/
axiom g_3 : g 3 = some 3

/-- g(4) = 5: Any 5 points contain an empty quadrilateral (Erdős) -/
axiom g_4 : g 4 = some 5

/-- g(5) = 10: Any 10 points contain an empty pentagon (Harborth 1978) -/
axiom g_5 : g 5 = some 10

/-- g(6) = 30: Any 30 points contain an empty hexagon (Heule-Scheucher 2024)

    This was a long-standing open problem. The existence of g(6) was proved
    independently by Nicolás (2007) and Gerken (2008). The exact value g(6) = 30
    was determined by Heule and Scheucher using SAT solvers. -/
axiom g_6 : g 6 = some 30

/-
## Part V: Horton's Theorem - g(k) Does Not Exist for k ≥ 7
-/

/-- Horton set: A configuration of n points with no empty 7-gon.
    Constructed recursively by taking two Horton sets of size n/2
    and "interlacing" them carefully. -/
def IsHortonSet (S : PointSet) : Prop :=
  InGeneralPosition S ∧ ¬ContainsEmptyKGon S 7

/-- Horton sets of arbitrary size exist -/
axiom horton_sets_exist :
  ∀ n : ℕ, ∃ S : PointSet, S.card = n ∧ IsHortonSet S

/-- Horton's Theorem (1983): g(7) does not exist.
    For any n, there exists a set of n points with no empty 7-gon. -/
theorem g_7_not_exists : g 7 = none := by
  -- The existence of arbitrarily large Horton sets implies g(7) = none
  unfold g
  simp only [dite_eq_right_iff]
  intro ⟨n, hn⟩
  obtain ⟨S, hS_card, hS_horton⟩ := horton_sets_exist n
  have h := hn S (le_of_eq hS_card) hS_horton.1
  exact hS_horton.2 h

/-- For all k ≥ 7, g(k) does not exist -/
axiom g_ge_7_not_exists : ∀ k : ℕ, k ≥ 7 → g k = none

/-
## Part VI: Bounds and Growth
-/

/-- For k ≤ 6, g(k) is finite -/
theorem g_exists_le_6 : ∀ k : ℕ, 3 ≤ k → k ≤ 6 → gExists k := by
  intro k hk3 hk6
  unfold gExists
  interval_cases k <;> simp [g_3, g_4, g_5, g_6]

/-
## Part VII: The Horton Construction
-/

/-- Base case: Horton set of 1 point -/
def hortonBase : PointSet := {![0, 0]}

/-
## Part VIII: Connection to Happy Ending Problem
-/

/-- The Happy Ending function g'(k): smallest n such that any n points
    contain a convex k-gon (not necessarily empty) -/
noncomputable def happyEnding (k : ℕ) : Option ℕ :=
  if h : ∃ n : ℕ, ∀ S : PointSet, S.card ≥ n → InGeneralPosition S →
    ∃ vertices ⊆ S, IsConvexKGon vertices k
  then some (Nat.find h)
  else none

/-- Erdős-Szekeres conjecture: g'(k) = 2^(k-2) + 1 -/
def erdos_szekeres_conjecture : Prop :=
  ∀ k : ℕ, k ≥ 3 → happyEnding k = some (2^(k-2) + 1)

/-
## Part IX: Computational Results
-/

/-
## Part X: Summary
-/

/--
**Erdős Problem #216: Partially Solved**

QUESTION: Does g(k) exist for all k? What are its values?

ANSWER:
- g(3) = 3 (trivial)
- g(4) = 5 (Erdős)
- g(5) = 10 (Harborth 1978)
- g(6) = 30 (Heule-Scheucher 2024)
- g(k) does NOT exist for k ≥ 7 (Horton 1983)

STATUS: Completely resolved. The function g(k) exists precisely for k ≤ 6.
-/
theorem erdos_216_summary :
    -- g exists for k = 3, 4, 5, 6
    (g 3 = some 3) ∧
    (g 4 = some 5) ∧
    (g 5 = some 10) ∧
    (g 6 = some 30) ∧
    -- g does not exist for k ≥ 7
    (g 7 = none) ∧
    (∀ k ≥ 7, g k = none) := by
  exact ⟨g_3, g_4, g_5, g_6, g_7_not_exists, g_ge_7_not_exists⟩

/-- The complete answer to Erdős Problem #216:
g(k) exists iff k ≤ 6, with known exact values, and the summary theorem. -/
theorem erdos_216 :
    (g 3 = some 3) ∧ (g 4 = some 5) ∧ (g 5 = some 10) ∧ (g 6 = some 30) ∧
    (g 7 = none) ∧ (∀ k ≥ 7, g k = none) :=
  erdos_216_summary

/-- Known values of g -/
theorem known_g_values :
    g 3 = some 3 ∧ g 4 = some 5 ∧ g 5 = some 10 ∧ g 6 = some 30 := by
  exact ⟨g_3, g_4, g_5, g_6⟩

/-- The threshold: g(k) exists iff k ≤ 6 -/
theorem g_exists_iff : ∀ k : ℕ, k ≥ 3 → (gExists k ↔ k ≤ 6) := by
  intro k hk3
  constructor
  · intro hExists
    by_contra hk7
    push_neg at hk7
    have := g_ge_7_not_exists k hk7
    unfold gExists at hExists
    simp [this] at hExists
  · intro hk6
    exact g_exists_le_6 k hk3 hk6

end Erdos216
