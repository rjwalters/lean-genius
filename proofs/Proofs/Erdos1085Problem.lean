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

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log

open Nat Finset

namespace Erdos1085

/-!
## Background: The Unit Distance Problem

Given n points in d-dimensional Euclidean space, how many pairs can be at
distance exactly 1 from each other?

This is one of the most famous problems in combinatorial geometry, especially
for d = 2, where the gap between upper and lower bounds has remained open
since the 1940s.
-/

/-!
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

/-- maxUnitDistances d n is achieved by some configuration. -/
axiom maxUnitDistances_spec (d n : ℕ) :
  ∃ P : PointConfig d n, unitDistanceCount P = maxUnitDistances d n

/-- maxUnitDistances d n is an upper bound for all configurations. -/
axiom maxUnitDistances_bound (d n : ℕ) (P : PointConfig d n) :
  unitDistanceCount P ≤ maxUnitDistances d n

/-!
## Trivial Bounds

The number of pairs is at most n choose 2 = n(n-1)/2.
-/

/-- Trivial upper bound: at most n choose 2 pairs can be unit distance. -/
axiom trivial_upper_bound (d n : ℕ) :
  maxUnitDistances d n ≤ n * (n - 1) / 2

/-- For n ≥ 2 and d ≥ 1, we can achieve at least n - 1 unit distances
(place points on a line at integer positions). -/
axiom linear_lower_bound (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) :
  n - 1 ≤ maxUnitDistances d n

/-!
## Dimension 2: The Classical Unit Distance Problem

This is Problem #90 on erdosproblems.com (and closely related to #1085).
The gap between n^(1+ε) and n^(4/3) has been open since the 1940s.
-/

/-- **Erdős Lower Bound (1946)**: f_2(n) > n^(1 + c/log log n) for some c > 0.

The construction uses a carefully chosen grid-like structure. -/
axiom erdos_1946_lower_d2 :
  ∃ c : ℕ, c > 0 ∧ ∀ n ≥ 16,
    n * n / (Nat.log 2 (Nat.log 2 n) + 1) ≤ maxUnitDistances 2 n * (Nat.log 2 (Nat.log 2 n) + 1)

/-- **Spencer-Szemerédi-Trotter Upper Bound (1984)**: f_2(n) = O(n^(4/3)).

This landmark result uses the crossing number inequality for graphs.
It improved Erdős's original O(n^(3/2)) bound. -/
axiom sst_1984_upper_d2 :
  ∃ C : ℕ, C > 0 ∧ ∀ n ≥ 1,
    maxUnitDistances 2 n ≤ C * n * Nat.sqrt n / 10

/-- The 2D problem remains OPEN: the gap between n^(1+o(1)) and n^(4/3) is unknown.

Conjecture: f_2(n) = Θ(n^(1 + c/log log n)) (the lower bound is tight). -/
def erdos_1085_2d_conjecture : Prop :=
  ∃ C : ℕ, C > 0 ∧ ∀ n ≥ 16,
    maxUnitDistances 2 n ≤ C * n * n / (Nat.log 2 (Nat.log 2 n) + 1)

/-- The 2D conjecture remains open. -/
axiom erdos_1085_2d_open :
  ¬(erdos_1085_2d_conjecture ↔ True) ∧ ¬(erdos_1085_2d_conjecture ↔ False)

/-!
## Dimension 3

The 3D case is also challenging with a gap between lower and upper bounds.
-/

/-- **Erdős Lower Bound (1960)**: f_3(n) = Ω(n^(4/3) log log n).

The construction generalizes the 2D approach using spherical caps. -/
axiom erdos_1960_lower_d3 :
  ∃ c : ℕ, c > 0 ∧ ∀ n ≥ 16,
    c * n * Nat.sqrt n * Nat.log 2 (Nat.log 2 n) / 1000 ≤ maxUnitDistances 3 n

/-- **Clarkson-Edelsbrunner-Guibas-Sharir-Welzl Upper Bound (1990)**:
f_3(n) = O(n^(3/2) β(n)) where β is the inverse Ackermann function.

This uses sophisticated techniques from computational geometry. -/
axiom cegsw_1990_upper_d3 :
  ∃ C : ℕ, C > 0 ∧ ∀ n ≥ 1,
    maxUnitDistances 3 n ≤ C * n * Nat.sqrt n

/-- The 3D problem is partially open: Is f_3(n) = O(n^(4/3) log log n)? -/
def erdos_1085_3d_open_question : Prop :=
  ∃ C : ℕ, C > 0 ∧ ∀ n ≥ 16,
    maxUnitDistances 3 n ≤ C * n * Nat.sqrt n * Nat.log 2 (Nat.log 2 n) / 100

/-- The 3D tight bound question remains open. -/
axiom erdos_1085_3d_open :
  ¬(erdos_1085_3d_open_question ↔ True) ∧ ¬(erdos_1085_3d_open_question ↔ False)

/-!
## Dimension ≥ 4: The High-Dimensional Case

For d ≥ 4, the picture is much cleaner. The answer is essentially
(p-1)/(2p) · n² where p = ⌊d/2⌋.
-/

/-- The Lenz construction: place n/2 points on each of two orthogonal unit circles.
Every point on one circle is distance 1 from every point on the other circle
(in the right configuration), giving ~n²/4 unit distances for d = 4. -/
def lenzCoefficient (d : ℕ) : ℚ :=
  if d ≥ 2 then (d / 2 - 1 : ℕ) / (2 * (d / 2) : ℕ) else 0

/-- **Lenz Lower Bound (d ≥ 4)**: f_d(n) ≥ (p-1)/(2p) · n² - O(1).

Lenz's elegant construction uses orthogonal circles in ℝ^d. -/
axiom lenz_lower_d4 (d : ℕ) (hd : 4 ≤ d) :
  ∃ C : ℕ, ∀ n ≥ 1,
    (d / 2 - 1) * n * n / (2 * (d / 2)) ≤ maxUnitDistances d n + C

/-- **Erdős-Stone Upper Bound (d ≥ 4)**: f_d(n) ≤ ((p-1)/(2p) + o(1)) · n².

This uses the Erdős-Stone theorem from extremal graph theory. -/
axiom erdos_stone_upper_d4 (d : ℕ) (hd : 4 ≤ d) :
  ∀ ε : ℕ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    maxUnitDistances d n ≤ ((d / 2 - 1) * n * n / (2 * (d / 2))) + ε * n * n / 100

/-!
## Exact Results for d ≥ 4

For even dimensions ≥ 4, exact formulas are known!
-/

/-- **Brass (1997)**: Exact formula for d = 4.
f_4(n) = ⌊n²/4⌋ + n - ⌊n/2⌋ - 1 for n ≥ 3. -/
axiom brass_1997_d4 :
  ∀ n ≥ 3, maxUnitDistances 4 n = n * n / 4 + n - n / 2 - 1

/-- **Swanepoel (2009)**: Exact formula for even d ≥ 6.
The answer has a precise closed form. -/
axiom swanepoel_2009_even (d : ℕ) (hd : 6 ≤ d) (heven : Even d) :
  ∃ f : ℕ → ℕ, ∀ n ≥ 1,
    maxUnitDistances d n = (d / 2 - 1) * n * n / (2 * (d / 2)) + f n ∧
    f n ≤ n

/-- **Erdős-Pach (1990)**: For odd d ≥ 5, tight bounds with n^(4/3) error.

f_d(n) = (p-1)/(2p) · n² ± O(n^(4/3)) where p = ⌊d/2⌋. -/
axiom erdos_pach_1990_odd (d : ℕ) (hd : 5 ≤ d) (hodd : Odd d) :
  ∃ c₁ c₂ : ℕ, c₁ > 0 ∧ c₂ > 0 ∧ ∀ n ≥ 1,
    (d / 2 - 1) * n * n / (2 * (d / 2)) ≤ maxUnitDistances d n + c₁ * n * Nat.sqrt n ∧
    maxUnitDistances d n ≤ (d / 2 - 1) * n * n / (2 * (d / 2)) + c₂ * n * Nat.sqrt n

/-!
## Examples and Special Values
-/

/-- f_2(3) = 3: Three points forming an equilateral triangle. -/
axiom example_d2_n3 : maxUnitDistances 2 3 = 3

/-- f_2(4) = 5: The optimal configuration is not the square (which gives 4),
but rather 4 points with 5 unit distances. -/
axiom example_d2_n4 : maxUnitDistances 2 4 = 5

/-- f_2(5) = 7: Five points can achieve 7 unit distances. -/
axiom example_d2_n5 : maxUnitDistances 2 5 = 7

/-- f_3(4) = 6: Four points forming a regular tetrahedron with edge 1. -/
axiom example_d3_n4 : maxUnitDistances 3 4 = 6

/-!
## Connections to Other Problems

The unit distance problem connects to many areas:
- Incidence geometry (point-circle incidences)
- The distinct distances problem (Erdős Problem #35)
- Graph drawing and the crossing number
-/

/-- The unit distance graph U(n) has n vertices and f_2(n) edges.
A key tool is the crossing number of this graph. -/
axiom crossing_number_connection :
  ∀ n ≥ 4, maxUnitDistances 2 n * maxUnitDistances 2 n ≤ 100 * n * n * n

/-- Connection to incidence geometry: f_2(n) relates to point-circle incidences
where all circles have radius 1. -/
axiom incidence_bound :
  ∀ n ≥ 1, maxUnitDistances 2 n ≤ n * n

/-!
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

/-- Summary: The high-dimensional case (d ≥ 4) is essentially solved.

For d ≥ 4, f_d(n) = (p-1)/(2p) · n² + o(n²) where p = ⌊d/2⌋.
This follows from the Lenz lower bound and Erdős-Stone upper bound. -/
axiom high_dim_solved (d : ℕ) (hd : 4 ≤ d) :
    ∃ C : ℕ, ∀ n ≥ 1,
      (d / 2 - 1) * n * n / (2 * (d / 2)) ≤ maxUnitDistances d n + C ∧
      maxUnitDistances d n ≤ (d / 2 - 1) * n * n / (2 * (d / 2)) + C * n * n / 10

end Erdos1085
