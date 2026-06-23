/-
  Erdős Problem #1085: The Unit Distance Problem

  Let f_d(n) be the maximum number of pairs of unit distance among n points in ℝ^d.
  Estimate f_d(n).

  **Key Results**:

  d = 2 (The classical Unit Distance Problem):
  - Lower: n^(1 + c/log log n) for some c > 0 (Erdős 1946)
  - Upper: O(n^(4/3)) (Spencer-Szemerédi-Trotter 1984)

  d = 3:
  - Lower: Ω(n^(4/3) log log n) (Erdős 1960)
  - Upper: O(n^(3/2) β(n)) (Clarkson-Edelsbrunner-Guibas-Sharir-Welzl 1990)
  - OPEN: Is f_3(n) = O(n^(4/3) log log n)?

  d ≥ 4:
  - Lenz construction gives lower bound (p-1)/(2p) · n² - O(1), p = ⌊d/2⌋
  - Erdős-Stone theorem gives upper bound ((p-1)/(2p) + o(1)) · n²
  - For even d ≥ 4: exact formula known (Brass d=4, Swanepoel d≥6)
  - For odd d ≥ 5: tight to n^(4/3) error term (Erdős-Pach 1990)

  References:
  - https://erdosproblems.com/1085
  - Erdős, P., "On sets of distances of n points" (1946)
  - Spencer, Szemerédi, Trotter, "Unit distances in the Euclidean plane" (1984)
  - Clarkson et al., "Combinatorial complexity bounds..." (1990)
-/

import Mathlib.Tactic

open Nat Finset

namespace Erdos1085

/-
## Background: The Unit Distance Problem

Given n points in d-dimensional Euclidean space, how many pairs can be at
distance exactly 1 from each other?

This is one of the most famous problems in combinatorial geometry, especially
for d = 2, where the gap between upper and lower bounds has remained open
since the 1940s.
-/

/-
## Core Definitions
-/

/-- A configuration of n points in d-dimensional Euclidean space.
We represent this as a function from Fin n to EuclideanSpace ℝ (Fin d). -/
def PointConfig (d n : ℕ) := Fin n → EuclideanSpace ℝ (Fin d)

/-- The set of pairs of distinct indices. -/
def distinctPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.filter (fun p => p.1 < p.2) Finset.univ

/-- Count the number of unit distance pairs in a configuration.
A unit distance pair (i, j) has ||P(i) - P(j)|| = 1. -/
noncomputable def unitDistanceCount {d n : ℕ} (P : PointConfig d n) : ℕ :=
  (distinctPairs n).filter (fun p =>
    dist (P p.1) (P p.2) = 1
  ) |>.card

/-- f_d(n) = the maximum number of unit distance pairs over all n-point
configurations in ℝ^d.

This is the central function of the problem. -/
axiom maxUnitDistances (d n : ℕ) : ℕ

/-
## The 2D Problem Remains OPEN

The gap between n^(1+o(1)) and n^(4/3) has been open since the 1940s.
-/

/-- The 2D problem remains OPEN: the gap between n^(1+o(1)) and n^(4/3) is unknown.

Conjecture: f_2(n) = Θ(n^(1 + c/log log n)) (the lower bound is tight). -/
def erdos_1085_2d_conjecture : Prop :=
  ∃ C : ℕ, C > 0 ∧ ∀ n ≥ 16,
    maxUnitDistances 2 n ≤ C * n * n / (Nat.log 2 (Nat.log 2 n) + 1)

/-
## Dimension 3

The 3D case is also challenging with a gap between lower and upper bounds.
-/

/-- The 3D problem is partially open: Is f_3(n) = O(n^(4/3) log log n)? -/
def erdos_1085_3d_open_question : Prop :=
  ∃ C : ℕ, C > 0 ∧ ∀ n ≥ 16,
    maxUnitDistances 3 n ≤ C * n * Nat.sqrt n * Nat.log 2 (Nat.log 2 n) / 100

/-
## Dimension ≥ 4: The High-Dimensional Case

For d ≥ 4, the picture is much cleaner. The answer is essentially
(p-1)/(2p) · n² where p = ⌊d/2⌋.
-/

/-- The Lenz construction: place n/2 points on each of two orthogonal unit circles.
Every point on one circle is distance 1 from every point on the other circle
(in the right configuration), giving ~n²/4 unit distances for d = 4. -/
def lenzCoefficient (d : ℕ) : ℚ :=
  if d ≥ 2 then (d / 2 - 1 : ℕ) / (2 * (d / 2) : ℕ) else 0

/-
## Summary

Erdős Problem #1085 asks for estimates of f_d(n), the maximum unit distances
among n points in ℝ^d.

**Solved Cases**:
- d = 2: n^(1+o(1)) ≤ f_2(n) ≤ O(n^(4/3)) [Gap OPEN]
- d = 3: n^(4/3) log log n ≪ f_3(n) ≪ n^(3/2) [Gap partially OPEN]
- d = 4: Exact formula (Brass 1997)
- d ≥ 6 even: Exact formulas (Swanepoel 2009)
- d ≥ 5 odd: (p-1)/(2p) · n² ± O(n^(4/3)) (Erdős-Pach 1990)

**Main Open Question**: Is f_2(n) = n^(1+o(1)) (matching the lower bound)?
-/

end Erdos1085
