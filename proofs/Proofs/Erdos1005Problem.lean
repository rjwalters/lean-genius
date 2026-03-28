import Mathlib.Data.Rat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-
# Erdős Problem #1005: Farey Fractions and Similar Ordering

## Problem Statement

Let f(n) be the length of the longest run of consecutive "similarly ordered"
Farey fractions of order n. Estimate f(n).

Is there a constant c > 0 such that f(n) = (c + o(1))·n?

## Known Results

- Lower bound: f(n) ≥ (1/12 - o(1))·n
- Upper bound: f(n) ≤ n/4 + O(1)
- The answer is conjectured to be f(n) ~ c·n for some c ∈ [1/12, 1/4]

## Background

The Farey sequence F_n consists of all fractions p/q with 0 ≤ p/q ≤ 1
and 1 ≤ q ≤ n, listed in increasing order. Two consecutive Farey fractions
a/b and c/d satisfy the mediant property: bc - ad = 1.

"Similarly ordered" likely refers to fractions whose denominators form
an increasing or decreasing run in the Farey sequence ordering.

Reference: https://erdosproblems.com/1005
-/

open Finset

namespace Erdos1005

-- ══════════════════════════════════════════════════════════════════
-- § 1: Farey Fractions
-- ══════════════════════════════════════════════════════════════════

/-- A Farey fraction of order n: a pair (p, q) with 0 ≤ p ≤ q, 1 ≤ q ≤ n,
    and gcd(p, q) = 1. -/
structure FareyFraction (n : ℕ) where
  p : ℕ
  q : ℕ
  hq_pos : 1 ≤ q
  hq_le : q ≤ n
  hp_le : p ≤ q
  hcoprime : Nat.Coprime p q

/-- The rational value of a Farey fraction. -/
def FareyFraction.toRat {n : ℕ} (f : FareyFraction n) : ℚ :=
  f.p / f.q

/-- Two consecutive Farey fractions satisfy the mediant property: bc - ad = 1. -/
def IsConsecutiveFarey {n : ℕ} (f g : FareyFraction n) : Prop :=
  g.p * f.q - f.p * g.q = 1

-- ══════════════════════════════════════════════════════════════════
-- § 2: The Longest Run
-- ══════════════════════════════════════════════════════════════════

/-- f(n) = the length of the longest run of consecutive similarly ordered
    Farey fractions in F_n. Axiomatized since the precise definition of
    "similarly ordered" requires the full Farey sequence construction. -/
axiom longestSimilarRun (n : ℕ) : ℕ

-- ══════════════════════════════════════════════════════════════════
-- § 3: Known Bounds
-- ══════════════════════════════════════════════════════════════════

/-- Lower bound: f(n) ≥ n/12 for large n. -/
axiom longestSimilarRun_lower :
  ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ →
    (longestSimilarRun n : ℝ) ≥ c * (n : ℝ)

/-- Upper bound: f(n) ≤ n/4 + O(1). -/
axiom longestSimilarRun_upper :
  ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ →
    (longestSimilarRun n : ℝ) ≤ (n : ℝ) / 4 + C

-- ══════════════════════════════════════════════════════════════════
-- § 4: The Conjecture
-- ══════════════════════════════════════════════════════════════════

/-- **Erdős Problem #1005** (OPEN): Is there a constant c > 0 such that
    f(n) = (c + o(1))·n? That is, does the longest similar run grow linearly
    with a definite leading constant? -/
axiom erdos_1005_conjecture :
  ∃ c : ℝ, c > 0 ∧ ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ →
    |(longestSimilarRun n : ℝ) / (n : ℝ) - c| < ε

-- ══════════════════════════════════════════════════════════════════
-- § 5: Basic Mediant Properties
-- ══════════════════════════════════════════════════════════════════

/-- If a/b < c/d are consecutive Farey fractions (bc - ad = 1),
    then c/d - a/b = 1/(bd). -/
theorem consecutive_farey_gap {n : ℕ} (f g : FareyFraction n)
    (h : IsConsecutiveFarey f g) (hf : f.toRat < g.toRat) :
    g.toRat - f.toRat = 1 / (f.q * g.q : ℚ) := by
  unfold FareyFraction.toRat
  have hfq : (f.q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hgq : (g.q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  unfold IsConsecutiveFarey at h
  push_cast [Nat.sub_eq_iff_eq_add] at h ⊢
  · linarith
  · -- Need g.p * f.q ≥ f.p * g.q (from f < g)
    by_contra hlt
    push_neg at hlt
    omega

/-- The number of Farey fractions of order n is approximately 3n²/π² + O(n log n). -/
-- This is a deep result (Möbius inversion); we don't formalize it here.

end Erdos1005
