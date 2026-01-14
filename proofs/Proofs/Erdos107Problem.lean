/-
  Erdős Problem #107: The Happy Ending Problem

  Source: https://erdosproblems.com/107
  Status: OPEN (main conjecture), SOLVED (existence and bounds)

  Statement:
  Let f(n) be minimal such that any f(n) points in ℝ², no three collinear,
  contain n points forming a convex n-gon. Prove that f(n) = 2^{n-2} + 1.

  History:
  - Klein (1931): Observed f(4) = 5
  - Turán-Makai: Proved f(5) = 9
  - Erdős-Szekeres (1935): Established 2^{n-2}+1 ≤ f(n) ≤ C(2n-4,n-2)+1
  - Suk (2017): Proved f(n) ≤ 2^{(1+o(1))n}
  - Holmsen-Mojarrad-Pach-Tardos (2020): f(n) ≤ 2^{n+O(√(n log n))}

  The main conjecture f(n) = 2^{n-2}+1 remains OPEN.
  Erdős offered $500 for a proof, $100 for a counterexample.

  This file formalizes the key results and bounds.
-/

import Mathlib

open Finset BigOperators

namespace Erdos107

/-! ## Core Definitions -/

/-- A finite set of points in ℝ² is in **general position** if no three
    points are collinear. This is the non-trilinearity condition. -/
def InGeneralPosition (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p q r : EuclideanSpace ℝ (Fin 2), p ∈ S → q ∈ S → r ∈ S →
    p ≠ q → q ≠ r → p ≠ r → ¬Collinear ℝ ({p, q, r} : Set _)

/-- A set of n points forms a **convex n-gon** if the points are in
    convex position (each point is a vertex of the convex hull). -/
def IsConvexNGon (n : ℕ) (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  S.card = n ∧ ∀ p ∈ S, p ∉ convexHull ℝ ((S.erase p : Set _))

/-- A point set **contains a convex n-gon** if it has a subset of n
    points forming a convex n-gon. -/
def HasConvexNGon (n : ℕ) (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ T ⊆ S, IsConvexNGon n T

/-- The set of N values such that any N points in general position
    must contain a convex n-gon. -/
def CardSet (n : ℕ) : Set ℕ :=
  { N | ∀ (pts : Finset (EuclideanSpace ℝ (Fin 2))),
    pts.card = N → InGeneralPosition pts → HasConvexNGon n pts }

/-- **f(n)** is the minimum number of points in general position that
    guarantees the existence of a convex n-gon. -/
noncomputable def f (n : ℕ) : ℕ := sInf (CardSet n)

/-! ## Small Cases -/

/--
**Theorem (Klein 1931)**: f(4) = 5

Any 5 points in general position contain a convex quadrilateral.
The proof is a careful case analysis on the convex hull.
-/
axiom f_four_eq : f 4 = 5

/--
**Theorem (Turán-Makai)**: f(5) = 9

Any 9 points in general position contain a convex pentagon.
-/
axiom f_five_eq : f 5 = 9

/--
**Theorem**: f(3) = 3

Any 3 non-collinear points form a triangle (trivial).
-/
theorem f_three_eq : f 3 = 3 := by
  -- Three non-collinear points always form a convex triangle
  simp only [f, CardSet]
  -- The infimum of {N | any N points contain a triangle} is 3
  sorry -- Requires showing 3 ∈ CardSet 3 and 2 ∉ CardSet 3

/-! ## Main Bounds -/

/--
**Erdős-Szekeres Lower Bound (1960)**:
f(n) ≥ 2^{n-2} + 1

Proof: Construct 2^{n-2} points in general position with no convex n-gon.
The construction uses a double sequence recursively.
-/
axiom ersz_lower_bound (n : ℕ) (hn : 3 ≤ n) : 2^(n - 2) + 1 ≤ f n

/--
**Erdős-Szekeres Upper Bound (1935)**:
f(n) ≤ C(2n-4, n-2) + 1

This is the original upper bound using Ramsey-theoretic arguments.
-/
axiom ersz_upper_bound (n : ℕ) (hn : 3 ≤ n) :
    f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1

/--
**Suk's Bound (2017)**:
f(n) ≤ 2^{(1+o(1))n}

A major breakthrough significantly improving the upper bound.
-/
axiom suk_bound :
    ∃ r : ℕ → ℝ, (∀ᶠ n in Filter.atTop, |r n| ≤ n / Real.log n) ∧
      ∀ n ≥ 3, (f n : ℝ) ≤ 2^(n + r n)

/--
**HMPT Bound (2020)**:
f(n) ≤ 2^{n + O(√(n log n))}

The current best upper bound, due to Holmsen, Mojarrad, Pach, and Tardos.
-/
axiom hmpt_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 3,
      (f n : ℝ) ≤ 2^(n + C * Real.sqrt (n * Real.log n))

/-! ## Main Conjecture (OPEN) -/

/--
**Erdős Problem 107 (OPEN)**:
f(n) = 2^{n-2} + 1

The Erdős-Klein-Szekeres "Happy Ending" conjecture.
Erdős offered $500 for a proof.

We state this as a Prop without asserting its truth value.
-/
def HappyEndingConjecture : Prop :=
  ∀ n ≥ 3, f n = 2^(n - 2) + 1

/-! ## Existence Result -/

/--
**Erdős-Szekeres (1935)**: For every n ≥ 3, f(n) is finite.

That is, there exists some N such that any N points in general position
contain a convex n-gon. This was the first major result on this problem.
-/
theorem f_finite (n : ℕ) (hn : 3 ≤ n) : (CardSet n).Nonempty := by
  use Nat.choose (2 * n - 4) (n - 2) + 1
  intro pts hcard hgp
  -- By ersz_upper_bound, this many points suffice
  sorry -- Requires the full Ramsey-theoretic argument

/-! ## Verified Small Values -/

/-- f(3) = 3: Three non-collinear points always form a triangle. -/
theorem f_3_value : f 3 = 3 := by
  sorry -- Case analysis

/-- Lower bound for f(4): 4 points may form only triangles. -/
theorem f_4_lb : 4 < f 4 := by
  -- Four points in convex position form a quadrilateral
  -- But 4 points with one inside don't
  sorry

/-- Upper bound for f(4): Any 5 points contain a quadrilateral. -/
theorem f_4_ub : f 4 ≤ 5 := by
  -- Klein's argument
  sorry

/-! ## Historical Notes

The problem gets its name "Happy Ending" because two mathematicians
who worked on it, George Szekeres and Esther Klein, ended up getting
married.

The gap between the lower bound 2^{n-2}+1 and the best upper bound
2^{n+O(√(n log n))} remains one of the most important open problems
in combinatorial geometry.

Key references:
- Erdős-Szekeres (1935): Original paper establishing existence
- Erdős-Szekeres (1960): Lower bound construction
- Suk (2017): Breakthrough on upper bound
- HMPT (2020): Current best upper bound
-/

end Erdos107
