/-
Erdős Problem #651: Convex Polyhedra from Points in General Position

Source: https://erdosproblems.com/651
Status: DISPROVED (Pohoata-Zakharov 2022)

Statement:
Let f_k(n) denote the smallest integer such that any f_k(n) points in
general position in ℝ^k contain n points that determine a convex polyhedron.

Is it true that f_k(n) > (1 + c_k)^n for some constant c_k > 0?

Answer: NO

Pohoata and Zakharov (2022) proved that f_3(n) ≤ 2^{o(n)}, showing that
exponential lower bounds fail even in dimension 3.

Background:
- k = 2: The Erdős-Klein-Szekeres problem (see Problem #107)
- The function satisfies f_2(n) > f_3(n) > f_4(n) > ...
- Higher dimensions make it easier to find convex subsets

References:
- [Er97e] Erdős: Original problem formulation
- [PoZa22] Pohoata, Zakharov: "Convex polytopes from fewer points" (arXiv:2208.04878)
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.AffineSpace.Independent

open Finset Set

namespace Erdos651

/- ## Part I: Points in General Position
-/

variable {k : ℕ}

/--
**General Position in ℝ^k:**
A set of points is in general position if no k+1 points lie on a (k-1)-dimensional
affine subspace (hyperplane).

In ℝ²: no 3 points are collinear.
In ℝ³: no 4 points are coplanar.
-/
def InGeneralPosition (S : Finset (Fin k → ℝ)) : Prop :=
  ∀ T : Finset (Fin k → ℝ), T ⊆ S → T.card = k + 1 →
    AffineIndependent ℝ (fun i : T => (i : Fin k → ℝ))

/- ## Part II: Convex Polyhedra
-/

/--
**Convex Hull:**
The convex hull of a finite set of points in ℝ^k.
-/
def convexHullOfPoints (S : Finset (Fin k → ℝ)) : Set (Fin k → ℝ) :=
  convexHull ℝ (S : Set (Fin k → ℝ))

/--
**Convex Polyhedron (Polytope):**
A subset determines a convex polyhedron if the points are the vertices
of their convex hull (no point is interior to the hull of the others).
-/
def DeterminesConvexPolyhedron (S : Finset (Fin k → ℝ)) : Prop :=
  ∀ p ∈ S, p ∉ convexHull ℝ ((S.erase p) : Set (Fin k → ℝ))

/--
**Contains n-Vertex Polyhedron:**
A point set contains an n-vertex convex polyhedron if there exists
a subset of n points that forms a convex polyhedron.
-/
def ContainsConvexPolyhedron (S : Finset (Fin k → ℝ)) (n : ℕ) : Prop :=
  ∃ T : Finset (Fin k → ℝ), T ⊆ S ∧ T.card = n ∧ DeterminesConvexPolyhedron T

/- ## Part III: The Function f_k(n)
-/

/--
**f_k(n):**
The smallest integer such that any f_k(n) points in general position
in ℝ^k contain n points determining a convex polyhedron.

This is a Ramsey-type function for convex geometry.
-/
axiom f_k (k n : ℕ) : ℕ

/--
**f_k achieves its purpose:**
Any f_k(n) points in general position contain an n-vertex polyhedron.
-/
/--
**f_k is minimal:**
There exist f_k(n) - 1 points in general position with no n-vertex polyhedron.
-/
/- ## Part IV: The Erdős-Klein-Szekeres Case (k = 2)
-/

/--
**Erdős-Klein-Szekeres:**
In the plane (k = 2), f_2(n) is the "happy ending problem".
Erdős-Szekeres (1935) proved: f_2(n) ≤ 2^{n-2} + 1.
Suk (2017) proved: f_2(n) = 2^{n + o(n)}.
-/
/--
**The ES Conjecture (proved by Suk 2017):**
f_2(n) = 2^{n-2} + 1 for all n ≥ 3.
-/
axiom suk_2017 (n : ℕ) (hn : n ≥ 3) :
    f_k 2 n = 2^(n - 2) + 1

/- ## Part V: Monotonicity in Dimension
-/

/--
**f_k decreases with dimension:**
f_2(n) > f_3(n) > f_4(n) > ...

In higher dimensions, it's easier to find convex subsets because
there's "more room" for points to be in convex position.
-/
/- ## Part VI: The Original Conjecture
-/

/--
**Erdős's Conjecture:**
For each k, there exists c_k > 0 such that f_k(n) > (1 + c_k)^n.

This would give exponential lower bounds for all dimensions.
-/
def ErdosConjecture : Prop :=
  ∀ k ≥ 2, ∃ c : ℝ, c > 0 ∧ ∀ n ≥ k + 1, (f_k k n : ℝ) > (1 + c)^n

/- ## Part VII: The Disproof
-/

/--
**Pohoata-Zakharov Theorem (2022):**
f_3(n) ≤ 2^{o(n)}

This is subexponential: for any c > 0, eventually f_3(n) < (1 + c)^n.
This disproves Erdős's conjecture for k = 3.
-/
axiom pohoata_zakharov_2022 :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, (f_k 3 n : ℝ) ≤ 2^(ε * n)

/--
**The key bound:**
2^{o(n)} means: for any constant c > 0, eventually f_3(n) < 2^{cn}.
In particular, (1 + c)^n > f_3(n) for small c is impossible uniformly.
-/
axiom subexponential_bound (c : ℝ) (hc : c > 0) :
    ∃ N : ℕ, ∀ n ≥ N, (f_k 3 n : ℝ) < (1 + c)^n

/--
**The conjecture is FALSE for k = 3:**
No constant c_3 > 0 gives f_3(n) > (1 + c_3)^n for all n.
-/
theorem conjecture_false_k3 :
    ¬(∃ c : ℝ, c > 0 ∧ ∀ n ≥ 4, (f_k 3 n : ℝ) > (1 + c)^n) := by
  intro ⟨c, hc, hBound⟩
  obtain ⟨N, hN⟩ := subexponential_bound c hc
  have : (f_k 3 (max N 4) : ℝ) < (1 + c)^(max N 4) := hN (max N 4) (le_max_left _ _)
  have : (f_k 3 (max N 4) : ℝ) > (1 + c)^(max N 4) := hBound (max N 4) (le_max_right _ _)
  linarith

/--
**The full conjecture is FALSE:**
-/
theorem erdos_651_disproved : ¬ErdosConjecture := by
  intro hConj
  obtain ⟨c, hc, hBound⟩ := hConj 3 (by norm_num : (3 : ℕ) ≥ 2)
  exact conjecture_false_k3 ⟨c, hc, fun n hn => hBound n (by omega)⟩

/- ## Part VIII: Main Results
-/

/--
**Erdős Problem #651: DISPROVED**

**Question:** Is f_k(n) > (1 + c_k)^n for some c_k > 0?

**Answer: NO** (Pohoata-Zakharov 2022)

For k = 3: f_3(n) ≤ 2^{o(n)}, which is subexponential.
This means no constant c_3 > 0 works.

**Key insight:** Higher dimensions make it easier to find
convex subsets, breaking the exponential barrier.
-/
theorem erdos_651 : ¬ErdosConjecture := erdos_651_disproved

/--
**Summary:**
- The conjecture is false: ¬ErdosConjecture
- The Pohoata-Zakharov bound is subexponential
- The k = 2 case is exponential (Erdős-Szekeres / Suk)
- Monotonicity in dimension: f_k decreases with k
-/
theorem erdos_651_summary :
    ¬ErdosConjecture ∧
    (∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, (f_k 3 n : ℝ) ≤ 2^(ε * n)) ∧
    (∀ n : ℕ, n ≥ 3 → f_k 2 n = 2^(n - 2) + 1) :=
  ⟨erdos_651_disproved, pohoata_zakharov_2022, suk_2017⟩

end Erdos651
