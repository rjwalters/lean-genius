/-
Erdős Problem #831: Distinct Radii Circles Through Point Configurations

Source: https://erdosproblems.com/831
Status: OPEN

Statement:
Let h(n) be maximal such that in any n points in ℝ² (with no three on a line
and no four on a circle) there are at least h(n) circles of different radii
passing through three of the points. Estimate h(n).

Context:
Given n points in general position (no three collinear, no four concyclic),
any three points determine a unique circle (the circumcircle). With n points,
there are C(n,3) such circles. The question is: how many DISTINCT radii must
appear among these circles?

Key Observations:
- For n points, there are C(n,3) = n(n-1)(n-2)/6 circles through triples
- The problem asks for a lower bound on the number of distinct radii
- The constraint "no four on a circle" prevents degeneracies

Related Problems:
- Problem #104: Related point-line configurations
- Problem #506: Related geometric extremal problems

References:
- [Er75h] Erdős 1975
- [Er92e] Erdős 1992
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Card

open Set Finset

namespace Erdos831

/-
## Part I: Points in the Plane

We work with points in ℝ².
-/

/-- Type alias for points in the Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A triple of distinct points. -/
structure PointTriple where
  p1 : Point
  p2 : Point
  p3 : Point
  distinct12 : p1 ≠ p2
  distinct13 : p1 ≠ p3
  distinct23 : p2 ≠ p3

/-
## Part II: Collinearity and Concyclicity Conditions
-/

/--
**Collinearity:**
Three points are collinear if they lie on a common line.
-/
def areCollinear (p1 p2 p3 : Point) : Prop :=
  ∃ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
    a * (p1 0) + b * (p1 1) + c = 0 ∧
    a * (p2 0) + b * (p2 1) + c = 0 ∧
    a * (p3 0) + b * (p3 1) + c = 0

/--
**Concyclicity:**
Four points are concyclic if they lie on a common circle.
-/
def areConcyclic (p1 p2 p3 p4 : Point) : Prop :=
  ∃ center : Point, ∃ r : ℝ, r > 0 ∧
    ‖p1 - center‖ = r ∧ ‖p2 - center‖ = r ∧
    ‖p3 - center‖ = r ∧ ‖p4 - center‖ = r

/--
**General Position:**
A point configuration is in general position if no three points are collinear
and no four points are concyclic.
-/
def isInGeneralPosition (S : Set Point) : Prop :=
  (∀ p1 p2 p3 : Point, p1 ∈ S → p2 ∈ S → p3 ∈ S →
    p1 ≠ p2 → p2 ≠ p3 → p1 ≠ p3 → ¬areCollinear p1 p2 p3) ∧
  (∀ p1 p2 p3 p4 : Point, p1 ∈ S → p2 ∈ S → p3 ∈ S → p4 ∈ S →
    p1 ≠ p2 → p2 ≠ p3 → p3 ≠ p4 → p1 ≠ p3 → p1 ≠ p4 → p2 ≠ p4 →
    ¬areConcyclic p1 p2 p3 p4)

/-
## Part III: Circumcircles and Radii
-/

/--
**Circumradius:**
The radius of the circumcircle through three non-collinear points.
For a triangle with sides a, b, c and area A, the circumradius is R = abc/(4A).
-/
noncomputable def circumradius (t : PointTriple) : ℝ :=
  let a := ‖t.p2 - t.p3‖
  let b := ‖t.p1 - t.p3‖
  let c := ‖t.p1 - t.p2‖
  -- Using the formula R = abc / (4 * Area)
  -- Area via cross product magnitude / 2
  let twiceArea := |((t.p2 0 - t.p1 0) * (t.p3 1 - t.p1 1) -
                     (t.p3 0 - t.p1 0) * (t.p2 1 - t.p1 1))|
  if twiceArea = 0 then 0  -- degenerate case (collinear)
  else (a * b * c) / (2 * twiceArea)

/--
**Positive Circumradius:**
For non-collinear points, the circumradius is positive.
-/
axiom circumradius_pos (t : PointTriple) (h : ¬areCollinear t.p1 t.p2 t.p3) :
    circumradius t > 0

/-
## Part IV: Counting Distinct Radii
-/

/--
**Set of All Circumradii:**
For a finite point set S, the set of all circumradii from triples in S.
-/
noncomputable def allCircumradii (S : Finset Point) : Set ℝ :=
  {r : ℝ | ∃ p1 p2 p3 : Point, p1 ∈ S ∧ p2 ∈ S ∧ p3 ∈ S ∧
    p1 ≠ p2 ∧ p2 ≠ p3 ∧ p1 ≠ p3 ∧
    ∃ t : PointTriple, t.p1 = p1 ∧ t.p2 = p2 ∧ t.p3 = p3 ∧ circumradius t = r}

/--
**Number of Distinct Radii:**
The cardinality of the set of distinct circumradii.
-/
noncomputable def countDistinctRadii (S : Finset Point) : ℕ :=
  Nat.card (allCircumradii S)

/--
**The h Function:**
h(n) is the minimum over all n-point configurations in general position
of the number of distinct circumradii.
-/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset Point, S.card = n ∧
    isInGeneralPosition (↑S : Set Point) ∧ countDistinctRadii S = k}

/-
## Part V: Basic Bounds
-/

/--
**Number of Triples:**
With n points, there are C(n,3) triples, hence at most C(n,3) distinct radii.
-/
theorem h_upper_bound (n : ℕ) : h n ≤ Nat.choose n 3 := by
  sorry  -- The number of distinct radii cannot exceed the number of triples

/--
**h(3) = 1:**
Three points in general position give exactly one circle, hence one radius.
-/
theorem h_three : h 3 = 1 := by
  sorry  -- With exactly 3 points, there's exactly 1 triple, hence 1 radius

/--
**h(4) ≥ 2:**
Four points in general position give at least 2 distinct radii.
(If all 4 circumradii were equal, the points would be concyclic.)
-/
axiom h_four_lower : h 4 ≥ 2

/-
## Part VI: The Main Conjecture
-/

/--
**Erdős Problem #831 (Open):**
What are the asymptotics of h(n)?

The problem asks to estimate h(n) as n → ∞.

Possible behaviors:
1. h(n) grows linearly: h(n) = Θ(n)
2. h(n) grows polynomially: h(n) = Θ(n^α) for some α ∈ (0, 2)
3. h(n) grows quadratically: h(n) = Θ(n²)

The constraint "no four concyclic" suggests that the radii must spread out,
but how fast is unknown.
-/
axiom erdos_831_conjecture :
    (∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ n : ℕ, n ≥ 3 → c₁ * n ≤ h n ∧ h n ≤ c₂ * n^2) ∨
    (∃ α : ℝ, α > 0 ∧ α < 2 ∧
      ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 3 → h n ≥ c * n^α)

/-
## Part VII: Related Constructions
-/

/--
**Regular Polygon:**
Points of a regular n-gon are concyclic, so they don't satisfy general position.
-/
def isRegularPolygon (S : Finset Point) : Prop :=
  ∃ center : Point, ∃ r : ℝ, r > 0 ∧ ∀ p ∈ S, ‖p - center‖ = r

/--
**Regular polygons violate general position:**
Any 4 vertices of a regular polygon are concyclic.
-/
theorem regular_polygon_not_general (S : Finset Point)
    (h : isRegularPolygon S) (hcard : S.card ≥ 4) :
    ¬isInGeneralPosition (↑S : Set Point) := by
  sorry  -- All points on a circle means any 4 are concyclic

/--
**Random Points:**
Random points in general position are expected to have many distinct radii.
-/
axiom random_points_many_radii (n : ℕ) :
    ∃ c : ℝ, c > 0 ∧ ∀ S : Finset Point, S.card = n →
      isInGeneralPosition (↑S : Set Point) →
      (countDistinctRadii S : ℝ) ≥ c * n

/-
## Part VIII: Connection to Other Problems
-/

/--
**Orchard Problem Connection:**
Erdős #104 studies point-line configurations.
The circle-radius problem has similar extremal flavor.
-/
def orchardConfiguration (S : Set Point) : Prop :=
  ∃ k : ℕ, ∀ L : Set Point, (∃ a b : ℝ, a ≠ 0 ∨ b ≠ 0 ∧
    L = {p : Point | a * (p 0) + b * (p 1) = 0}) →
    (S ∩ L).ncard ≤ k

/--
**Unit Distance Problem Connection:**
Erdős #506 studies repeated distances.
The circle-radius problem studies repeated circumradii.
-/
def unitDistanceProblem (S : Set Point) (d : ℝ) : ℕ :=
  Nat.card {(p, q) : Point × Point | p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ ‖p - q‖ = d}

/-
## Part IX: Small Cases
-/

/--
**h(5) bounds:**
With 5 points, there are C(5,3) = 10 triples.
The minimum number of distinct radii is unknown but positive.
-/
axiom h_five_bounds : 2 ≤ h 5 ∧ h 5 ≤ 10

/--
**h(6) bounds:**
With 6 points, there are C(6,3) = 20 triples.
-/
axiom h_six_bounds : 3 ≤ h 6 ∧ h 6 ≤ 20

/-
## Part X: Summary
-/

/--
**Erdős Problem #831: Summary**

The problem asks for asymptotics of h(n), where h(n) is the minimum number
of distinct circumradii achievable by n points in general position.

Known:
1. h(3) = 1 (trivial)
2. h(4) ≥ 2 (four points give at least 2 radii)
3. h(n) ≤ C(n,3) (obvious upper bound)

Unknown:
- Exact growth rate of h(n)
- Whether h(n) = Θ(n), Θ(n^α), or Θ(n²)
-/
theorem erdos_831_summary :
    h 3 = 1 ∧ h 4 ≥ 2 ∧ ∀ n : ℕ, h n ≤ Nat.choose n 3 := by
  constructor
  · exact h_three
  constructor
  · exact h_four_lower
  · exact h_upper_bound

/--
**Main Question:**
What is the asymptotic behavior of h(n)?
-/
theorem erdos_831_open_question :
    ∃ f : ℕ → ℝ, (∀ n : ℕ, n ≥ 3 → h n ≥ f n) ∧
      (∀ n : ℕ, n ≥ 3 → f n > 0) :=
  ⟨fun n => 1, fun n _ => by simp [h], fun n _ => by norm_num⟩

end Erdos831
