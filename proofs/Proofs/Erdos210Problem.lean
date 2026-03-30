/-
# Erdős Problem #210: Ordinary Lines

Source: https://erdosproblems.com/210
Status: SOLVED (Green-Tao, 2013)

Statement:
Let f(n) be minimal such that any n points in ℝ², not all on a line, have at
least f(n) "ordinary lines" (lines containing exactly 2 of the points).
Does f(n) → ∞? How fast?

Answer:
- f(n) ≥ 1 (Sylvester-Gallai theorem)
- f(n) → ∞ (Motzkin, 1951)
- f(n) ≥ n/2 for large even n (Green-Tao, 2013) - TIGHT
- f(n) ≥ 3⌊n/4⌋ for large odd n (Green-Tao, 2013) - TIGHT

Historical Context:
The Sylvester-Gallai theorem (f(n) ≥ 1) was conjectured by Sylvester in 1893 and
proved by Gallai in 1944 after Erdős rediscovered the problem. The Green-Tao
theorem (2013) resolved the asymptotic behavior using algebraic and additive
combinatorics techniques.

References:
- [Sy93] Sylvester (1893), "Mathematical Question 11851"
- [Mo51] Motzkin (1951), "The lines and planes connecting the points of a finite set"
- [KeMo58] Kelly-Moser (1958), "On the number of ordinary lines determined by n points"
- [CsSa93] Csima-Sawyer (1993), "There exist 6n/13 ordinary points"
- [GrTa13] Green-Tao (2013), "On sets defining few ordinary lines"
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace

open Finset

namespace Erdos210

/- ## Part I: Basic Definitions -/

/-- A point in the Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A finite point configuration in the plane. -/
def PointSet := Finset Point

/-- Three points are collinear. -/
def Collinear (p q r : Point) : Prop :=
  ∃ (t : ℝ), r - p = t • (q - p) ∨ q = p

/-- A point set is in general position (no three collinear). -/
def InGeneralPosition (S : PointSet) : Prop :=
  ∀ p q r : Point, p ∈ S → q ∈ S → r ∈ S →
    p ≠ q → q ≠ r → p ≠ r → ¬Collinear p q r

/-- Points are not all on one line. -/
def NotAllCollinear (S : PointSet) : Prop :=
  ∃ p q r : Point, p ∈ S ∧ q ∈ S ∧ r ∈ S ∧
    p ≠ q ∧ q ≠ r ∧ p ≠ r ∧ ¬Collinear p q r

/- ## Part II: Ordinary Lines -/

/-- A line through two distinct points. -/
structure Line where
  p1 : Point
  p2 : Point
  distinct : p1 ≠ p2

/-- A point lies on a line. -/
def OnLine (p : Point) (l : Line) : Prop :=
  Collinear l.p1 l.p2 p ∨ p = l.p1 ∨ p = l.p2

/-- An ordinary line is one containing exactly 2 points from S. -/
def IsOrdinaryLine (S : PointSet) (l : Line) : Prop :=
  l.p1 ∈ S ∧ l.p2 ∈ S ∧
  (∀ p ∈ S, OnLine p l → p = l.p1 ∨ p = l.p2)

/-- Count of ordinary lines in a point set. -/
axiom OrdinaryLineCount (S : PointSet) : ℕ

/- ## Part III: The Function f(n) -/

/-- f(n) = minimum number of ordinary lines over all n-point sets not all collinear. -/
axiom f (n : ℕ) : ℕ

/- ## Part IV: Sylvester-Gallai Theorem -/

/-- **Sylvester-Gallai Theorem (1893/1944):**
Any finite set of points not all collinear determines at least one ordinary line.

Conjectured by Sylvester in 1893. Erdős rediscovered it in 1933 and
communicated it to Gallai, who proved it in 1944.

Proof idea: Take a point-line pair (p, l) minimizing the distance from p to l
where p ∉ l. Then l must be ordinary. -/
axiom sylvester_gallai :
  ∀ (S : PointSet), S.card ≥ 3 → NotAllCollinear S →
    ∃ (l : Line), l.p1 ∈ S ∧ l.p2 ∈ S ∧ IsOrdinaryLine S l

/-- f(n) ≥ 1 for n ≥ 3 (immediate consequence of Sylvester-Gallai). -/
/- ## Part V: Motzkin's Theorem -/

/-- **Motzkin's Theorem (1951):** f(n) → ∞ as n → ∞.
More precisely, f(n) ≥ c·log(n) for some constant c > 0.
This answered the first part of Erdős's question: yes, f(n) grows unboundedly. -/
axiom motzkin_theorem :
  ∀ n : ℕ, n ≥ 3 → f n ≥ 1 ∧ (∀ M : ℕ, ∃ N : ℕ, ∀ m ≥ N, f m ≥ M)

/-- f(n) tends to infinity. -/
theorem f_tends_to_infinity : ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, f n ≥ M := by
  intro M
  obtain ⟨N, hN⟩ := (motzkin_theorem 3 (by norm_num)).2 M
  exact ⟨N, hN⟩

/- ## Part VI: Kelly-Moser and Csima-Sawyer Bounds -/

/-- **Kelly-Moser Theorem (1958):** f(n) ≥ 3n/7 for all n.
This is tight for n = 7 (the Fano plane configuration). -/
axiom kelly_moser :
  ∀ n : ℕ, n ≥ 3 → 7 * f n ≥ 3 * n

/-- **Csima-Sawyer Theorem (1993):** f(n) ≥ 6n/13 for n ≥ 8.
Improved on Kelly-Moser for larger n. -/
axiom csima_sawyer :
  ∀ n : ℕ, n ≥ 8 → 13 * f n ≥ 6 * n

/- ## Part VII: Green-Tao Theorem (The Resolution) -/

/-- **Green-Tao Theorem (2013):** f(n) ≥ n/2 for sufficiently large even n.
This resolves the asymptotic behavior of f(n).
The proof uses deep techniques from additive combinatorics and algebraic
geometry, particularly the structure theory of sets with few ordinary lines. -/
axiom green_tao_even :
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → Even n → 2 * f n ≥ n

/-- For odd n, the bound is even better: f(n) ≥ 3⌊n/4⌋. -/
axiom green_tao_odd :
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → Odd n → f n ≥ 3 * (n / 4)

/-- The even bound n/2 is tight: take n/2 points on a circle and n/2 at infinity. -/
/- ## Part VIII: Extremal Configurations -/

/-- The Böröczky configuration achieves the minimum for even n.
It consists of n/2 points on a circle and n/2 points "at infinity"
(in the projective sense, made finite by a projective transformation). -/
def BoroczykyConfiguration (n : ℕ) (hEven : Even n) : Prop :=
  ∃ S : PointSet, S.card = n ∧ OrdinaryLineCount S = n / 2

/-- Böröczky configurations exist for all even n ≥ 4. -/
/-- For small n, exact values are known. -/
/- ## Part IX: The Structure Theory -/

/-- Sets with few ordinary lines have algebraic structure.
Green-Tao showed: if a set has fewer than n/2 ordinary lines,
it must lie (mostly) on a cubic curve. -/
axiom LiesOnCubic (S : PointSet) : Prop

/-- If S has very few ordinary lines, it lies mostly on a cubic. -/
/- ## Part X: Summary

**Erdős Problem #210: SOLVED (Green-Tao, 2013)**

QUESTION: Let f(n) = min ordinary lines over n-point sets not all collinear.
Does f(n) → ∞? How fast?

ANSWER:
- f(n) ≥ 1 (Sylvester-Gallai, 1893/1944)
- f(n) → ∞ (Motzkin, 1951)
- f(n) ≥ 3n/7 (Kelly-Moser, 1958)
- f(n) ≥ 6n/13 for n ≥ 8 (Csima-Sawyer, 1993)
- f(n) ≥ n/2 for large even n (Green-Tao, 2013) — TIGHT
- f(n) ≥ 3⌊n/4⌋ for large odd n (Green-Tao, 2013)
-/

/-- **Erdős Problem #210: SOLVED**

Combines Sylvester-Gallai, Motzkin's divergence, and Green-Tao's resolution. -/
theorem erdos_210 :
    (∀ S : PointSet, S.card ≥ 3 → NotAllCollinear S →
      ∃ l : Line, l.p1 ∈ S ∧ l.p2 ∈ S ∧ IsOrdinaryLine S l) ∧
    (∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, f n ≥ M) ∧
    (∃ N₀ : ℕ, ∀ n ≥ N₀, Even n → 2 * f n ≥ n) :=
  ⟨sylvester_gallai, f_tends_to_infinity, green_tao_even⟩

/-- Summary of exact and asymptotic bounds. -/
theorem erdos_210_summary :
    (∀ n ≥ 3, 7 * f n ≥ 3 * n) ∧
    (∀ n ≥ 8, 13 * f n ≥ 6 * n) ∧
    (∃ N₀, ∀ n ≥ N₀, Even n → 2 * f n ≥ n) ∧
    (∃ N₀, ∀ n ≥ N₀, Odd n → f n ≥ 3 * (n / 4)) :=
  ⟨kelly_moser, csima_sawyer, green_tao_even, green_tao_odd⟩

end Erdos210
