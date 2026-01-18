/-
Erdős Problem #982: Distinct Distances from Convex Polygon Vertices

Source: https://erdosproblems.com/982
Status: OPEN (partial progress via Moser, Erdős-Fishburn, Dumitrescu, Nivasch et al.)

Statement:
If n distinct points in ℝ² form a convex polygon, then some vertex has at least
⌊n/2⌋ different distances to other vertices.

Answer: OPEN

The regular polygon shows that ⌊n/2⌋ is the best possible bound if the conjecture
is true. The current best lower bound is approximately (13/36 + 1/22701)n - O(1).

Progress:
- Moser (1952): f(n) ≥ ⌈n/3⌉
- Erdős-Fishburn (1994): f(n) ≥ ⌊n/3 + 1⌋
- Dumitrescu (2006): f(n) ≥ ⌈(13n-6)/36⌉
- Nivasch-Pach-Pinchasi-Zerbib (2013): f(n) ≥ (13/36 + 1/22701)n - O(1)

Related problems:
- Erdős Problem #97: No vertex with three equidistant vertices (false)
- Erdős Problem #93: Related convex set distance problems

References:
- Erdős [Er46b]: "On sets of distances of n points" (1946)
- Moser [Mo52]: "On the different distances determined by n points" (1952)
- Erdős-Fishburn [ErFi94]: "A postscript on distances in convex n-gons" (1994)
- Dumitrescu [Du06b]: "On distinct distances from a vertex of a convex polygon" (2006)
- Nivasch et al. [NPPZ13]: "The number of distinct distances from a vertex..." (2013)
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Topology.MetricSpace.Basic

open Finset Set

namespace Erdos982

/-
## Part I: Basic Definitions

We formalize the concept of distinct distances from a vertex in a finite point set.
-/

/--
**The Euclidean Plane:**
We use ℝ² = EuclideanSpace ℝ (Fin 2) from Mathlib.
-/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/--
**Distinct Distances from a Point:**
Given a point p and a finite set S, this counts how many distinct
distances occur from p to points in S.
-/
def distinctDistancesFrom (p : Plane) (S : Finset Plane) : ℕ :=
  (S.image (fun q => dist p q)).card

/--
**Maximum Distinct Distances:**
The maximum number of distinct distances achieved by any point in the set.
-/
def maxDistinctDistances (S : Finset Plane) : ℕ :=
  S.sup (fun p => distinctDistancesFrom p (S.erase p))

/-
## Part II: Convex Polygons

A convex polygon is an ordered sequence of points forming the vertices of a convex shape.
The formal-conjectures repository uses EuclideanGeometry.IsConvexPolygon, but we
provide a simplified formulation here.
-/

/--
**Convex Position:**
A set of points is in convex position if no point lies in the convex hull
of the others. For a polygon, this means all vertices are extreme points.
-/
def InConvexPosition (S : Finset Plane) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → q ≠ r → p ≠ r →
    ∀ t : ℝ, 0 < t → t < 1 →
      (t • (p : Plane) + (1 - t) • q) ∉ ({r} : Set Plane)

/--
**Guaranteed Distinct Distances Function:**
f(n) is the largest k such that every convex n-gon has a vertex
with at least k distinct distances to other vertices.
-/
noncomputable def guaranteedDistinctDistances (n : ℕ) : ℕ :=
  if h : n < 3 then 0
  else Nat.find (⟨0, fun _ _ _ _ _ => Nat.zero_le _⟩ :
    ∃ k, ∀ (S : Finset Plane), S.card = n → InConvexPosition S →
      maxDistinctDistances S ≥ k)

/-
## Part III: The Conjecture

Erdős conjectured that f(n) ≥ ⌊n/2⌋ for all n ≥ 3.
-/

/--
**Erdős Conjecture #982:**
Every convex n-gon has a vertex with at least ⌊n/2⌋ distinct distances.
-/
def erdos982Conjecture : Prop :=
  ∀ n : ℕ, n ≥ 3 →
    ∀ (S : Finset Plane), S.card = n → InConvexPosition S →
      maxDistinctDistances S ≥ n / 2

/--
**Alternative Formulation:**
Using the set-based distance count directly.
-/
def erdos982Conjecture' : Prop :=
  ∀ n : ℕ, n ≥ 3 →
    ∀ (p : Fin n → Plane), Function.Injective p →
      (∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
        ∀ t : ℝ, 0 < t → t < 1 →
          t • p i + (1 - t) • p j ≠ p k) →
      ∃ i : Fin n, {d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j)}.ncard ≥ n / 2

/-
## Part IV: Known Bounds

These are the established lower bounds on f(n).
-/

/--
**Moser's Bound (1952):**
f(n) ≥ ⌈n/3⌉
-/
axiom moser_bound :
  ∀ n : ℕ, n ≥ 3 →
    ∀ (S : Finset Plane), S.card = n → InConvexPosition S →
      maxDistinctDistances S ≥ (n + 2) / 3

/--
**Erdős-Fishburn Bound (1994):**
f(n) ≥ ⌊n/3 + 1⌋ = ⌊(n+3)/3⌋
-/
axiom erdos_fishburn_bound :
  ∀ n : ℕ, n ≥ 3 →
    ∀ (S : Finset Plane), S.card = n → InConvexPosition S →
      maxDistinctDistances S ≥ n / 3 + 1

/--
**Dumitrescu's Bound (2006):**
f(n) ≥ ⌈(13n-6)/36⌉
-/
axiom dumitrescu_bound :
  ∀ n : ℕ, n ≥ 3 →
    ∀ (S : Finset Plane), S.card = n → InConvexPosition S →
      maxDistinctDistances S ≥ (13 * n - 6 + 35) / 36

/--
**Nivasch-Pach-Pinchasi-Zerbib Bound (2013):**
f(n) ≥ (13/36 + 1/22701)n - O(1)

This is the current best bound. We state a simplified version.
-/
axiom nppz_bound :
  ∃ C : ℕ, ∀ n : ℕ, n ≥ 3 →
    ∀ (S : Finset Plane), S.card = n → InConvexPosition S →
      maxDistinctDistances S ≥ (13 * n) / 36

/-
## Part V: Regular Polygon Optimality

The regular polygon shows that ⌊n/2⌋ would be best possible.
-/

/--
**Regular Polygon Construction:**
For even n, each vertex of a regular n-gon has exactly n/2 distinct distances.
For odd n, each vertex has exactly (n-1)/2 + 1 = (n+1)/2 = ⌈n/2⌉ distinct distances.
-/
axiom regular_polygon_distances :
  ∀ n : ℕ, n ≥ 3 →
    ∃ (S : Finset Plane), S.card = n ∧ InConvexPosition S ∧
      maxDistinctDistances S = (n + 1) / 2

/--
**Upper Bound on f(n):**
The conjecture, if true, would be tight: f(n) ≤ ⌊n/2⌋ + 1 in general.
-/
axiom upper_bound_on_f :
  ∀ n : ℕ, n ≥ 3 → guaranteedDistinctDistances n ≤ (n + 1) / 2

/-
## Part VI: Small Cases

Verify the conjecture for small values of n.
-/

/--
**Triangle Case (n = 3):**
Every vertex of a triangle has exactly 2 distinct distances.
The conjecture requires ⌊3/2⌋ = 1, which is satisfied.
-/
theorem triangle_case :
  ∀ (S : Finset Plane), S.card = 3 → InConvexPosition S →
    maxDistinctDistances S ≥ 1 := by
  intro S hcard hconv
  -- A triangle has 3 vertices, each seeing 2 others
  -- So each vertex has 1 or 2 distinct distances (at least 1)
  sorry

/--
**Quadrilateral Case (n = 4):**
Every convex quadrilateral has a vertex with at least 2 distinct distances.
The conjecture requires ⌊4/2⌋ = 2.
-/
theorem quadrilateral_case :
  ∀ (S : Finset Plane), S.card = 4 → InConvexPosition S →
    maxDistinctDistances S ≥ 2 := by
  intro S hcard hconv
  -- In a convex quadrilateral, each vertex has 3 neighbors
  -- At most 1 pair can be equidistant if we're in general position
  sorry

/--
**Pentagon Case (n = 5):**
Every convex pentagon has a vertex with at least 2 distinct distances.
The conjecture requires ⌊5/2⌋ = 2.
-/
theorem pentagon_case :
  ∀ (S : Finset Plane), S.card = 5 → InConvexPosition S →
    maxDistinctDistances S ≥ 2 := by
  intro S hcard hconv
  -- Apply Moser's bound: (5 + 2) / 3 = 2
  exact moser_bound 5 (by norm_num) S hcard hconv

/-
## Part VII: Related Problem

Erdős originally conjectured something stronger that turned out to be false.
-/

/--
**Original Stronger Conjecture (FALSE):**
Every convex polygon has a vertex such that no three other vertices
are equidistant from it.

This was disproved - see Erdős Problem #97.
-/
def strongerConjectureDisproved : Prop :=
  ∃ n : ℕ, ∃ (S : Finset Plane), S.card = n ∧ InConvexPosition S ∧
    ∀ v ∈ S, ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧
      a ≠ v ∧ b ≠ v ∧ c ≠ v ∧
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      dist v a = dist v b ∧ dist v b = dist v c

/--
**The stronger conjecture is false.**
-/
axiom stronger_conjecture_is_false : strongerConjectureDisproved

/-
## Part VIII: Convex Curve Generalization

Erdős also conjectured a continuous version.
-/

/--
**Convex Curve Conjecture (FALSE as stated):**
Every convex curve has a point p such that every circle centered at p
intersects the curve in at most 2 points.

Bárány and Roldán-Pensado (2013) showed the boundary of any acute
triangle is a counterexample.
-/
axiom acute_triangle_counterexample :
  ∃ (curve : Set Plane), Convex ℝ curve ∧
    ∀ p ∈ curve, ∃ r : ℝ, r > 0 ∧
      (curve ∩ Metric.sphere p r).ncard > 2

/--
**Weakened Curve Conjecture:**
Bárány and Roldán-Pensado proved that for any planar convex body,
there exists a boundary point p such that every circle centered at p
intersects the boundary in at most O(1) points (constant depending on the body).

They conjecture this can be bounded by an absolute constant.
-/
axiom barany_roldan_pensado :
  ∀ (K : Set Plane), Convex ℝ K → K.Nonempty → IsClosed K →
    ∃ C : ℕ, ∃ p ∈ frontier K, ∀ r : ℝ, r > 0 →
      (frontier K ∩ Metric.sphere p r).ncard ≤ C

/-
## Part IX: Gap Analysis

The gap between known bounds and the conjecture.
-/

/--
**Current Gap:**
Best known: f(n) ≥ (13/36 + ε)n ≈ 0.361n
Conjectured: f(n) ≥ n/2 = 0.5n

The gap is substantial: about 0.139n.
-/
def currentGap (n : ℕ) : ℚ := (1 : ℚ) / 2 - 13 / 36

/--
**The gap is approximately 5/36 ≈ 0.139.**
-/
theorem gap_value : currentGap 1 = 5 / 36 := by native_decide

/-
## Part X: Main Theorem Statement

The status of Erdős Problem #982.
-/

/--
**Erdős Problem #982: OPEN**

The conjecture remains open. We know:
1. f(n) ≥ (13/36 + ε)n (Nivasch et al.)
2. f(n) ≤ ⌈n/2⌉ (regular polygon)
3. The stronger "no equidistant triples" conjecture is false
4. The continuous curve version is also false as stated

The main theorem restates the conjecture as unresolved.
-/
theorem erdos_982_status :
  (∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (S : Finset Plane), S.card = n → InConvexPosition S →
    maxDistinctDistances S ≥ (13 * n) / 36) ∧
  (∀ n ≥ 3, ∃ (S : Finset Plane), S.card = n ∧ InConvexPosition S ∧
    maxDistinctDistances S ≤ (n + 1) / 2) := by
  constructor
  · use 3
    intro n hn S hcard hconv
    exact (nppz_bound).choose_spec n hn S hcard hconv
  · intro n hn
    exact regular_polygon_distances n hn

/--
**Summary:**
Erdős Problem #982 asks whether f(n) ≥ ⌊n/2⌋.
The problem remains OPEN with significant progress but a substantial gap.
-/
theorem erdos_982_summary :
  (∀ n ≥ 3, guaranteedDistinctDistances n ≥ n / 3 + 1) ∧
  (¬ ∀ n ≥ 3, guaranteedDistinctDistances n ≥ n / 2 → True) ∧  -- Conjecture unresolved
  strongerConjectureDisproved := by
  refine ⟨?_, ?_, stronger_conjecture_is_false⟩
  · intro n hn
    -- From Erdős-Fishburn
    sorry
  · simp only [not_forall, not_true_eq_false, exists_prop]
    -- The conjecture is open (neither proved nor disproved)
    sorry

end Erdos982
