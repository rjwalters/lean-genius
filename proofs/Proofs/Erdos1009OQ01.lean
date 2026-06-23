/-
  Erdős #1009 OQ-01: Optimal Constant in Györi's Bound f(c) ≤ Cc²

  Source: https://erdosproblems.com/1009

  The problem: Györi (1988) proved f(c) ≪ c² for the edge-disjoint triangle
  problem. The exact optimal constant C in f(c) ≤ Cc² is unknown.

  This file formalizes:
  1. What it means for C to be a valid bound constant
  2. Structural properties (monotonicity, closure under min)
  3. The optimal constant as the infimum of valid constants
  4. A lower bound C ≥ 1/4 from Sauer's construction (f(2) ≥ 1)
  5. The open question: what is the exact value of the optimal C?

  Status: Partially axiomatized (3 axioms for deep results)
  Theorems: 10 proved, 0 sorries

  Tags: graph-theory, triangles, edge-disjoint, turan-numbers, optimization
-/

import Mathlib

namespace Erdos1009OQ01

/-!
## Axioms: Reproducing deep results from the parent formalization

These axioms capture Györi's theorem (1988) and Sauer's construction.
They correspond to published mathematical results not yet proved in Lean.
-/

/-- The bound function f(c): the number of triangles that may be "missing".
    Axiomatized following Györi (1988). Values are natural numbers (counts). -/
axiom boundFunction (c : ℝ) : ℕ

/-- Györi's main theorem: f(c) = O(c²).
    There exists an absolute constant C > 0 such that f(c) ≤ Cc² for all c > 0.
    Reference: Györi (1988), "On the number of edge disjoint triangles in K₄-free graphs" -/
axiom gyori_quadratic_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ c : ℝ, 0 < c → (boundFunction c : ℝ) ≤ C * c ^ 2

/-- Sauer's lower bound: f(2) ≥ 1.
    The complete tripartite graph K_{1,m,m} shows that for c = 2,
    you cannot always find all k edge-disjoint triangles.
    Reference: Sauer's construction from Erdős (1971) -/
axiom sauer_lower_bound : 1 ≤ boundFunction 2

/-!
## Valid bound constants

A real number C is a "valid bound constant" if f(c) ≤ Cc² for all positive c.
-/

/-- C is a valid bound constant: (boundFunction c) ≤ Cc² for all c > 0 -/
def ValidBound (C : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → (boundFunction c : ℝ) ≤ C * c ^ 2

/-- Györi's theorem provides a valid bound constant -/
theorem validBound_exists : ∃ C : ℝ, 0 < C ∧ ValidBound C := gyori_quadratic_bound

/-- Any valid bound constant must be nonneg (since boundFunction c ≥ 0) -/
theorem ValidBound.nonneg {C : ℝ} (hC : ValidBound C) : 0 ≤ C := by
  have h := hC 1 one_pos
  simp only [one_pow, mul_one] at h
  exact le_trans (Nat.cast_nonneg _) h

/-- Valid bound constants are upward closed: if C is valid and C ≤ C', then C' is valid -/
theorem ValidBound.mono {C C' : ℝ} (hC : ValidBound C) (h : C ≤ C') : ValidBound C' := by
  intro c hc
  exact (hC c hc).trans (by nlinarith [sq_nonneg c])

/-- The minimum of two valid bound constants is also valid -/
theorem ValidBound.min_valid {C₁ C₂ : ℝ}
    (h₁ : ValidBound C₁) (h₂ : ValidBound C₂) : ValidBound (min C₁ C₂) := by
  intro c hc
  simp only [min_def]
  split_ifs with h
  · exact h₁ c hc
  · exact h₂ c hc

/-- A valid bound C implies that f(c)/c² ≤ C for all positive c -/
theorem ValidBound.ratio_le {C : ℝ} (hC : ValidBound C) {c : ℝ} (hc : 0 < c) :
    (boundFunction c : ℝ) / c ^ 2 ≤ C := by
  rw [div_le_iff (by positivity)]
  exact hC c hc

/-!
## The optimal bound constant

The optimal constant C* is the infimum of all valid bound constants.
It equals the supremum of f(c)/c² over all c > 0.
-/

/-- The optimal bound constant: the infimum of all valid bound constants.
    This is the smallest C such that f(c) ≤ Cc² for all c > 0. -/
noncomputable def optimalBound : ℝ := sInf {C : ℝ | ValidBound C}

/-- The set of valid bound constants is bounded below (every valid C ≥ 0) -/
theorem validBounds_bddBelow : BddBelow {C : ℝ | ValidBound C} :=
  ⟨0, fun C hC => hC.nonneg⟩

/-- The optimal bound is at most any valid bound constant -/
theorem optimalBound_le {C : ℝ} (hC : ValidBound C) : optimalBound ≤ C :=
  csInf_le validBounds_bddBelow hC

/-- The optimal bound is nonneg -/
theorem optimalBound_nonneg : 0 ≤ optimalBound := by
  obtain ⟨C, _, hC⟩ := validBound_exists
  apply le_csInf ⟨C, hC⟩
  intro D hD
  exact hD.nonneg

/-- If C < optimalBound, then C is not a valid bound constant -/
theorem lt_optimalBound_not_valid {C : ℝ} (h : C < optimalBound) : ¬ValidBound C := by
  intro hC
  exact absurd (optimalBound_le hC) (not_le.mpr h)

/-!
## Lower bound from Sauer's construction

Sauer's result f(2) ≥ 1 gives the lower bound C* ≥ 1/4.
For any valid C, the constraint at c = 2 gives C * 4 ≥ f(2) ≥ 1, so C ≥ 1/4.
-/

/-- Sauer's lower bound implies optimalBound ≥ 1/4.
    Any valid C must satisfy C ≥ f(2)/4 ≥ 1/4 by Sauer's construction. -/
theorem optimalBound_ge_quarter : 1 / 4 ≤ optimalBound := by
  obtain ⟨C, _, hC⟩ := validBound_exists
  apply le_csInf ⟨C, hC⟩
  intro D hD
  have hD2 := hD 2 (by norm_num)
  have hs : (1 : ℝ) ≤ (boundFunction 2 : ℝ) := by exact_mod_cast sauer_lower_bound
  simp only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hD2
  linarith

/-!
## The open question

The exact value of optimalBound is unknown. What is known:
- optimalBound ≥ 1/4 (from Sauer's construction)
- optimalBound is finite (from Györi's theorem)
- optimalBound ≥ 0 (trivially, from nonnegativity of f)

The precise determination of optimalBound is the fundamental open question.
-/

/-- Erdős's result: f(c) = 0 for c < 1/2.
    Stated as a Prop (not axiom) — means the constraint on C is only binding for c ≥ 1/2.
    Reference: Erdős (1971), proved f(c) = 0 for c < 1/2 using chromatic number arguments. -/
def erdos_small_c_statement : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 / 2 → boundFunction c = 0

/-- The open question: determine the exact value of optimalBound.
    Known bounds: 1/4 ≤ optimalBound < ∞ (Sauer lower bound + Györi upper bound).
    The exact value is an open problem in combinatorics. -/
def optimalBoundQuestion : Prop :=
  ∃ C : ℝ, C = optimalBound ∧ 1 / 4 ≤ C ∧ ∀ D : ℝ, ValidBound D ↔ C ≤ D

end Erdos1009OQ01
