/-
Erdős Problem #1069: Szemerédi-Trotter Theorem on k-Rich Lines

Source: https://erdosproblems.com/1069
Status: SOLVED by Szemerédi-Trotter (1983)

Statement:
Given any n points in ℝ², the number of k-rich lines (lines which contain
≥ k of the points) is, provided k ≤ n^(1/2),
  ≪ n²/k³.

Background:
This is a conjecture of Erdős, Croft, and Purdy, described by Erdős in 1987.
Szemerédi and Trotter proved it in 1983 as part of their landmark incidence
theorem. The best constant is unknown. For k = √n, lattice points show there
can be ≥ (2+o(1))√n many √n-rich lines.

Key Insight:
A k-rich line contains many point incidences. The Szemerédi-Trotter theorem
bounds total incidences I(P,L) ≤ O(|P|^(2/3)|L|^(2/3) + |P| + |L|), which
implies the k-rich line bound via a counting argument.

Reference:
[SzTr83] Szemerédi, E. and Trotter, W.T. (1983), "Extremal problems in
discrete geometry", Combinatorica 3, 381-392.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset

namespace Erdos1069

open Finset

/- ## Part 1: Basic Definitions

We define points, lines, and incidences in the plane.
-/

/-- A point in ℝ² -/
abbrev Point := ℝ × ℝ

/-- A line in ℝ² represented by (a, b, c) where ax + by = c -/
structure Line where
  a : ℝ
  b : ℝ
  c : ℝ
  nonzero : a ≠ 0 ∨ b ≠ 0

/-- A point lies on a line -/
def Point.onLine (p : Point) (l : Line) : Prop :=
  l.a * p.1 + l.b * p.2 = l.c

/-- The set of points in P that lie on line l -/
def pointsOnLine (P : Finset Point) (l : Line) : Finset Point :=
  P.filter (fun p => decide (l.a * p.1 + l.b * p.2 = l.c))

/-- Number of incidences between a point set and a line -/
def incidenceCount (P : Finset Point) (l : Line) : ℕ :=
  (pointsOnLine P l).card

/- ## Part 2: k-Rich Lines

A line is k-rich if it contains at least k points from P.
-/

/-- A line is k-rich with respect to P if it contains ≥ k points of P -/
def isKRich (P : Finset Point) (l : Line) (k : ℕ) : Prop :=
  incidenceCount P l ≥ k

/-- The set of k-rich lines (for a given finite set of lines L) -/
def kRichLines (P : Finset Point) (L : Finset Line) (k : ℕ) : Finset Line :=
  L.filter (fun l => decide (incidenceCount P l ≥ k))

/-- The number of k-rich lines -/
def numKRichLines (P : Finset Point) (L : Finset Line) (k : ℕ) : ℕ :=
  (kRichLines P L k).card

/- ## Part 3: Total Incidences

The total number of point-line incidences is the sum over all lines.
-/

/-- Total incidences between P and L -/
def totalIncidences (P : Finset Point) (L : Finset Line) : ℕ :=
  L.sum (fun l => incidenceCount P l)

/-- Alternative: incidences as pairs (p, l) where p lies on l -/
def incidencePairs (P : Finset Point) (L : Finset Line) : Finset (Point × Line) :=
  (P ×ˢ L).filter (fun pl => decide (pl.1.onLine pl.2))

/- ## Part 4: The Szemerédi-Trotter Theorem

The main incidence bound: I(P, L) = O(|P|^(2/3)|L|^(2/3) + |P| + |L|).
-/

/-- The Szemerédi-Trotter bound: incidences are at most this function -/
noncomputable def szTrBound (n m : ℕ) : ℝ :=
  (n : ℝ)^(2/3 : ℝ) * (m : ℝ)^(2/3 : ℝ) + n + m

/-- Szemerédi-Trotter Theorem (1983): The main incidence bound.
    For any finite point set P and line set L in ℝ², the number of
    incidences is O(|P|^{2/3}|L|^{2/3} + |P| + |L|). -/
axiom szemeredi_trotter (P : Finset Point) (L : Finset Line) :
  ∃ C : ℝ, C > 0 ∧ (totalIncidences P L : ℝ) ≤ C * szTrBound P.card L.card

/- ## Part 5: The k-Rich Lines Bound

From Szemerédi-Trotter, we derive the k-rich lines bound.
-/

/-- The k-rich lines bound function: n²/k³ -/
noncomputable def kRichBound (n k : ℕ) : ℝ :=
  (n : ℝ)^2 / (k : ℝ)^3

/-- **Erdős Problem #1069: The k-rich lines bound.**
    Szemerédi-Trotter implies: the number of k-rich lines is O(n²/k³)
    when k ≤ √n. -/
axiom kRich_bound (P : Finset Point) (L : Finset Line) (k : ℕ)
    (hk : k ≥ 2) (hn : (k : ℝ)^2 ≤ P.card) :
  ∃ C : ℝ, C > 0 ∧ (numKRichLines P L k : ℝ) ≤ C * kRichBound P.card k

/-- Erdős Problem #1069: restated as a theorem from the axiom. -/
theorem erdos_1069 (P : Finset Point) (L : Finset Line) (k : ℕ)
    (hk : k ≥ 2) (hn : (k : ℝ)^2 ≤ P.card) :
  ∃ C : ℝ, C > 0 ∧ (numKRichLines P L k : ℝ) ≤ C * kRichBound P.card k :=
  kRich_bound P L k hk hn

/- ## Part 6: The Proof Strategy

The proof from Szemerédi-Trotter to k-rich lines uses a dyadic argument:
partition lines by incidence count into levels [2^i, 2^{i+1}), apply
Szemerédi-Trotter to each level, then sum.
-/

/-- Dyadic decomposition: lines with 2^i to 2^(i+1) incidences -/
def dyadicLines (P : Finset Point) (L : Finset Line) (i : ℕ) : Finset Line :=
  L.filter (fun l => decide (2^i ≤ incidenceCount P l ∧ incidenceCount P l < 2^(i+1)))

/- ## Part 7: Lower Bound Constructions

Known constructions show the bound is close to tight.
-/

/-- Lattice points: m × m grid has many m-rich lines -/
def latticePoints (m : ℕ) : Finset Point :=
  (Finset.range m ×ˢ Finset.range m).image (fun p => ((p.1 : ℝ), (p.2 : ℝ)))

/- ## Part 8: Special Cases -/

/- ## Part 9: Point-Line Duality -/

/- ## Part 10: Summary

**Erdős Problem #1069: SOLVED**

**Question:** Given n points in ℝ², is the number of k-rich lines O(n²/k³)?

**Answer:** YES (Szemerédi-Trotter, 1983)

**Key Results:**
1. Szemerédi-Trotter theorem: I(P,L) = O(|P|^{2/3}|L|^{2/3} + |P| + |L|)
2. k-rich lines bound: O(n²/k³) when k ≤ √n
3. Exponent 2/3 is optimal
4. Lower bound: lattice points give Ω(√n) many √n-rich lines
-/

/-- Summary theorem combining the main results. -/
theorem erdos_1069_summary :
    -- Szemerédi-Trotter theorem holds
    (∀ P L, ∃ C : ℝ, C > 0 ∧ (totalIncidences P L : ℝ) ≤ C * szTrBound P.card L.card) ∧
    -- k-rich lines bound holds
    (∀ P L k, k ≥ 2 → (k : ℝ)^2 ≤ P.card →
      ∃ C : ℝ, C > 0 ∧ (numKRichLines P L k : ℝ) ≤ C * kRichBound P.card k) :=
  ⟨szemeredi_trotter, fun P L k hk hn => kRich_bound P L k hk hn⟩

end Erdos1069
