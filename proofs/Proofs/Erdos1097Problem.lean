/-!
# Erdős Problem #1097 — Common Differences in Three-Term Arithmetic Progressions

Let A be a set of n integers. How many distinct d can occur as the
common difference of a three-term arithmetic progression in A?
Are there always O(n^{3/2}) many such d?

## Status: OPEN

## Key Results

- **Erdős–Spencer**: Probabilistic construction achieving n^{3/2} common
  differences.
- **Erdős–Ruzsa**: Explicit construction achieving n^{1+c} for some c > 0.
- **Katz–Tao (1999)**: Upper bound f(n) ≤ C · n^{11/6}.
- **Lemm (2015)**: Lower bound f(n) ≥ n^{1.77898...}.
- **AlphaEvolve (2025)**: Slight improvement on Lemm's lower bound.

Current gap: 1.778... ≤ c ≤ 11/6 ≈ 1.833.

## Equivalent Formulation

The problem is equivalent to Bourgain's sums-differences problem: find
the smallest c such that |A −_G B| ≤ C · max(|A|, |B|, |A +_G B|)^c.
This connects to the Kakeya conjecture via Bourgain's arithmetic approach.

*Reference:* [erdosproblems.com/1097](https://www.erdosproblems.com/1097)
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

/-! ## Core Definitions -/

/-- A three-term AP with base a and common difference d in set A:
a, a+d, a+2d all belong to A. -/
def IsThreeAP (A : Set ℤ) (a d : ℤ) : Prop :=
  a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A

/-- The set of common differences of three-term APs in A:
  D(A) = { d : ∃ a, {a, a+d, a+2d} ⊆ A }. -/
def commonDifferences (A : Set ℤ) : Set ℤ :=
  { d | ∃ a, IsThreeAP A a d }

/-- Finite version: common differences of a finite integer set. -/
noncomputable def commonDiffFinset (A : Finset ℤ) : Finset ℤ :=
  (A - A).filter fun d => ∃ a ∈ A, a + d ∈ A ∧ a + 2 * d ∈ A

/-- Count of distinct common differences |D(A)|. -/
noncomputable def numCommonDiff (A : Finset ℤ) : ℕ :=
  (commonDiffFinset A).card

/-! ## Main Conjecture -/

/-- **Erdős Problem #1097 (Open).**
Is f(n) = O(n^{3/2})? That is, does there exist C such that every
n-element set A of integers satisfies |D(A)| ≤ C · n^{3/2}? -/
def erdos_1097_conjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (A : Finset ℤ), A.card = n →
    (numCommonDiff A : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2)

/-! ## Upper Bound -/

/-- **Katz–Tao (1999).** f(n) ≤ C · n^{11/6} for some absolute constant C.
This is the best known upper bound on the exponent. -/
axiom katz_tao_upper :
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (A : Finset ℤ), A.card = n →
    (numCommonDiff A : ℝ) ≤ C * (n : ℝ) ^ ((11 : ℝ) / 6)

/-! ## Lower Bounds -/

/-- **Erdős–Spencer.** Probabilistic construction: there exist n-element
sets with at least C · n^{3/2} common differences. -/
axiom erdos_spencer_lower :
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
    ∃ A : Finset ℤ, A.card = n ∧
      (numCommonDiff A : ℝ) ≥ C * (n : ℝ) ^ ((3 : ℝ) / 2)

/-- **Erdős–Ruzsa.** Explicit construction achieving n^{1+c} for some c > 0. -/
axiom erdos_ruzsa_explicit :
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
    ∃ A : Finset ℤ, A.card = n ∧
      (numCommonDiff A : ℝ) ≥ C * (n : ℝ) ^ (1 + c)

/-- **Lemm (2015).** There exist sets achieving exponent > 1.778. -/
axiom lemm_lower :
  ∃ c : ℝ, c > 1.778 ∧ ∀ (n : ℕ), 0 < n →
    ∃ A : Finset ℤ, A.card = n ∧
      (numCommonDiff A : ℝ) ≥ (n : ℝ) ^ c

/-- **AlphaEvolve (2025).** Slight improvement on Lemm's lower bound
using automated search methods. -/
axiom alphaevolve_improvement :
  ∃ c : ℝ, c > 1.77898 ∧ ∀ (n : ℕ), 0 < n →
    ∃ A : Finset ℤ, A.card = n ∧
      (numCommonDiff A : ℝ) ≥ (n : ℝ) ^ c

/-! ## Bourgain's Sums-Differences Equivalence -/

/-- Restricted sum: { a + b : (a,b) ∈ G }. -/
def restrictedSum (G : Finset (ℤ × ℤ)) : Finset ℤ :=
  G.image fun p => p.1 + p.2

/-- Restricted difference: { a − b : (a,b) ∈ G }. -/
def restrictedDiff (G : Finset (ℤ × ℤ)) : Finset ℤ :=
  G.image fun p => p.1 - p.2

/-- **Bourgain's sums-differences exponent.** The exponent c holds if
|A −_G B| ≤ C · max(|A|, |B|, |A +_G B|)^c for all A, B, G ⊆ A × B. -/
def BourgainExponent (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (A B : Finset ℤ) (G : Finset (ℤ × ℤ)),
      G ⊆ A ×ˢ B →
      ((restrictedDiff G).card : ℝ) ≤
        C * ((max (max A.card B.card) (restrictedSum G).card : ℕ) : ℝ) ^ c

/-- **Chan's Equivalence.** The optimal exponent for common differences
equals the critical Bourgain exponent. This connects the combinatorial
3-AP problem to harmonic analysis and the Kakeya conjecture. -/
axiom chan_equivalence :
  ∀ c : ℝ, c ≥ 1 →
    (∀ (n : ℕ), 0 < n →
      ∃ A : Finset ℤ, A.card = n ∧ (numCommonDiff A : ℝ) ≥ (n : ℝ) ^ c) ↔
    ¬BourgainExponent c

/-! ## Summary -/

/-- The current state of knowledge: 1.778 < c* ≤ 11/6 ≈ 1.833. -/
theorem current_bounds_summary :
    (∃ c : ℝ, c > 1.778 ∧ ∀ (n : ℕ), 0 < n →
      ∃ A : Finset ℤ, A.card = n ∧ (numCommonDiff A : ℝ) ≥ (n : ℝ) ^ c) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (A : Finset ℤ), A.card = n →
      (numCommonDiff A : ℝ) ≤ C * (n : ℝ) ^ ((11 : ℝ) / 6)) :=
  ⟨lemm_lower, katz_tao_upper⟩
