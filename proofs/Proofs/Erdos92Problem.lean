/-
Erdős Problem #92: Equidistant Points in the Plane

Let f(n) be maximal such that there exists a set A of n points in ℝ²
where every x ∈ A has at least f(n) points in A equidistant from x.

Is it true that f(n) ≤ n^{o(1)}? Or even f(n) < n^{c/log log n}?

**Status**: OPEN

**Known Bounds**:
- Lower: f(n) > n^{c/log log n} (lattice points)
- Upper: f(n) ≪ n^{4/11} (JJMT 2024)

**Prize**: $500 for proof of f(n) ≤ n^{o(1)}

Reference: https://erdosproblems.com/92
-/

import Mathlib

open Filter Finset
open scoped Topology

namespace Erdos92

/-!
## Background

This problem concerns the equidistance structure of point sets in the plane.

For each point x in a set A, consider how many other points lie on circles
centered at x. The function f(n) asks: what's the best we can guarantee
for ALL points simultaneously?

This is related to the unit distance problem (Problem #90).
-/

/--
The **distance** between two points in ℝ².
-/
noncomputable def dist' (x y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ‖x - y‖

/--
For a point x and a set of points, **maxEquidistantPoints x A** is the
maximum number of points in A that are equidistant from x.

This counts the size of the largest "circle" centered at x through points of A.
-/
noncomputable def maxEquidistantPoints (x : EuclideanSpace ℝ (Fin 2))
    (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  let otherPoints := A.erase x
  let distances := otherPoints.image (dist' x)
  sSup (distances.image fun d => (otherPoints.filter fun p => dist' x p = d).card)

/--
A set A has the **k-equidistant property** if every point x ∈ A has at least
k other points at the same distance from x.
-/
def hasEquidistantProperty (k : ℕ) (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  A.Nonempty ∧ ∀ x ∈ A, k ≤ maxEquidistantPoints x A

/--
The set of achievable k values for n-point sets.
-/
noncomputable def achievableValues (n : ℕ) : Set ℕ :=
  {k | ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))), A.card = n ∧ hasEquidistantProperty k A}

/--
**f(n)** is the maximum k such that some n-point set has the k-equidistant property.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sSup (achievableValues n)

/-!
## The Main Questions

Erdős asked two related questions about the growth of f(n).
-/

/--
**Weak Conjecture (OPEN)**

Is f(n) ≤ n^{o(1)}? That is, for any ε > 0, is f(n) ≤ n^ε eventually?

This asks whether f(n) grows slower than any positive power of n.
-/
def WeakConjecture : Prop :=
  ∀ ε : ℝ, ε > 0 → ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ)^ε

/--
**Strong Conjecture (OPEN)**

Is f(n) < n^{c/log log n} for some constant c > 0?

This is a more precise form of the weak conjecture.
-/
def StrongConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
    (f n : ℝ) ≤ (n : ℝ)^(c / Real.log (Real.log n))

/-!
## Known Bounds
-/

/--
**Trivial Upper Bound**

f(n) ≤ n - 1 since any point can have at most n - 1 other points equidistant.
-/
theorem f_le_n_minus_one (n : ℕ) (hn : n ≥ 1) : f n ≤ n - 1 := by
  sorry

/--
**Square Root Bound**

f(n) ≪ √n. This follows from basic counting arguments.
-/
axiom sqrtBound :
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ c * Real.sqrt n

/--
**Pach-Sharir Bound (1992)**

f(n) ≪ n^{2/5}. This uses incidence geometry bounds.
-/
axiom pachSharirBound :
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ c * (n : ℝ)^(2/5 : ℝ)

/--
**JJMT Bound (2024)**

f(n) ≪ n^{4/11}. This is the best known upper bound, from circle-point
incidence bounds by Janzer, Janzer, Methuku, and Tardos.
-/
axiom jjmtBound :
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ c * (n : ℝ)^(4/11 : ℝ)

/--
**Lattice Lower Bound**

f(n) > n^{c/log log n} for some c > 0. The √n × √n integer lattice achieves this.
-/
axiom latticeLowerBound :
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
    (n : ℝ)^(c / Real.log (Real.log n)) ≤ f n

/-!
## Small Values

Fishburn computed exact values for small n.
-/

/--
**f(6) = 3**: 6 is the smallest n with f(n) = 3.
-/
axiom f_6_eq_3 : f 6 = 3

/--
**f(8) = 4**: 8 is the smallest n with f(n) = 4.
-/
axiom f_8_eq_4 : f 8 = 4

/-!
## Consequences

The weak conjecture would imply strong bounds on unit distance graphs.
-/

/--
If the weak conjecture holds, then the strong conjecture is strictly stronger
(it gives a more precise bound).
-/
theorem strong_implies_weak (h : StrongConjecture) : WeakConjecture := by
  intro ε hε
  obtain ⟨c, hc_pos, hc⟩ := h
  filter_upwards [hc] with n hn
  sorry -- need: c/log log n ≤ ε eventually

/-!
## Historical Notes

This problem is a "stronger form" of the unit distance conjecture (Problem #90).
It was studied by Erdős and Fishburn, who computed small cases and noted that
lattice points may not give optimal constructions.

The recent improvement to n^{4/11} by JJMT (2024) uses sophisticated
incidence geometry techniques.
-/

end Erdos92
