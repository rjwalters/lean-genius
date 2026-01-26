/-!
# Erdős Problem #507 — Heilbronn's Triangle Problem

Let α(n) be the smallest value such that every set of n points in
the unit disk contains three points forming a triangle of area ≤ α(n).
Estimate α(n).

**Status: OPEN.**

Lower bound: α(n) ≫ (log n)/n² (Komlós–Pintz–Szemerédi, 1982)
Upper bound: α(n) ≪ 1/n^{8/7+o(1)} → 1/n^{7/6+o(1)}
  (Komlós–Pintz–Szemerédi 1981; Cohen–Pohoata–Zakharov 2024)

The exact exponent of n in α(n) is unknown.

Reference: https://erdosproblems.com/507
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The area of the triangle determined by three points in ℝ². -/
noncomputable def triangleArea (p q r : ℝ × ℝ) : ℝ :=
  |p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)| / 2

/-- A point configuration in the unit disk. -/
def IsInUnitDisk (P : Finset (ℝ × ℝ)) : Prop :=
  ∀ p ∈ P, p.1 ^ 2 + p.2 ^ 2 ≤ 1

/-- The minimum triangle area over all triples from a point set. -/
noncomputable def minTriangleArea (P : Finset (ℝ × ℝ)) : ℝ :=
  ⨅ (p ∈ P) (q ∈ P) (r ∈ P) (_ : p ≠ q) (_ : q ≠ r) (_ : p ≠ r),
    triangleArea p q r

/-- Heilbronn's function: the supremum of minimum triangle areas
    over all n-point configurations in the unit disk. -/
noncomputable def heilbronn (n : ℕ) : ℝ :=
  sSup { α : ℝ | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ IsInUnitDisk P ∧
    ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, p ≠ q → q ≠ r → p ≠ r →
      triangleArea p q r ≥ α }

/-! ## Trivial Bounds -/

/-- Erdős's observation: α(n) ≫ 1/n² from a greedy argument.
    Place points one at a time; each new point avoids O(n²) thin
    strips of total area O(1/n). -/
axiom lower_bound_trivial :
    ∃ c > 0, ∀ n : ℕ, 1 ≤ n → heilbronn n ≥ c / (n : ℝ) ^ 2

/-- Trivial upper bound: α(n) ≪ 1/n from pigeonhole.
    Divide the disk into n/3 strips of width O(1/n); some strip
    contains 3 points forming a thin triangle. -/
axiom upper_bound_trivial :
    ∃ C > 0, ∀ n : ℕ, 3 ≤ n → heilbronn n ≤ C / (n : ℝ)

/-! ## Komlós–Pintz–Szemerédi Lower Bound -/

/-- The KPS (1982) lower bound: α(n) ≫ (log n)/n².
    This improves the trivial 1/n² bound by a logarithmic factor,
    using a sophisticated probabilistic argument. -/
axiom kps_lower_bound :
    ∃ c > 0, ∀ n : ℕ, 2 ≤ n →
      heilbronn n ≥ c * Real.log n / (n : ℝ) ^ 2

/-! ## Upper Bounds -/

/-- Komlós–Pintz–Szemerédi (1981): α(n) ≪ n^{-8/7}.
    The first improvement over the trivial 1/n bound, using
    the Szemerédi regularity lemma. -/
axiom kps_upper_bound :
    ∃ C > 0, ∀ n : ℕ, 3 ≤ n →
      heilbronn n ≤ C / (n : ℝ) ^ (8/7 : ℝ)

/-- Cohen–Pohoata–Zakharov (2024): α(n) ≪ n^{-7/6-o(1)}.
    The current best upper bound, improving the KPS exponent
    from 8/7 ≈ 1.143 to 7/6 ≈ 1.167. Uses incidence geometry
    and the polynomial method. -/
axiom cpz_upper_bound :
    ∃ C > 0, ∀ n : ℕ, 3 ≤ n →
      heilbronn n ≤ C / (n : ℝ) ^ (7/6 : ℝ)

/-! ## Main Open Question -/

/-- The gap between (log n)/n² and 1/n^{7/6} is enormous.
    The true exponent β such that α(n) = n^{-β+o(1)} is unknown.
    We have 7/6 ≤ β ≤ 2. -/
axiom heilbronn_exponent_range :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      heilbronn n ≤ (n : ℝ) ^ (-(7:ℝ)/6 + ε) ∧
      heilbronn n ≥ (n : ℝ) ^ (-(2:ℝ) - ε)

/-! ## Related Results -/

/-- In higher dimensions d ≥ 3, the analogous problem asks for
    the minimum volume simplex. Less is known; the gap is wider. -/
axiom higher_dimensional_analog (d : ℕ) (hd : 3 ≤ d) :
    ∃ c C > 0, ∀ n : ℕ, d + 1 ≤ n →
      c / (n : ℝ) ^ d ≤ heilbronn n ∧ heilbronn n ≤ C / (n : ℝ)
