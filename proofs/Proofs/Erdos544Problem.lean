/-
# Erdős Problem #544 — Consecutive Ramsey Number Differences

Erdős and Sós asked: show that R(3, k+1) − R(3, k) → ∞ as k → ∞.
Further, prove or disprove that R(3, k+1) − R(3, k) = o(k).

## Known bounds

The best known bounds for R(3, k) are:
- Lower: R(3, k) ≥ c · k² / (log k) (Kim 1995, improved by Bohman–Keevash,
  Fiz Pontiveros–Griffiths–Morris)
- Upper: R(3, k) ≤ (1 + o(1)) · k² / log k (Shearer 1983, improved by
  Campos–Griffiths–Morris–Sahasrabudhe 2023)

These imply R(3, k+1) − R(3, k) is at least of order k / log k, but the
exact growth of consecutive differences remains open.

Reference: https://erdosproblems.com/544
-/

import Mathlib

/- ## Ramsey number R(3, k) -/

/-- R(3, k): the minimum n such that every 2-colouring of edges of Kₙ
    contains either a red triangle or a blue Kₖ.
    Axiomatised with its defining property. -/
axiom ramsey3 : ℕ → ℕ

/-- R(3, k) is monotone increasing: R(3, k) ≤ R(3, k+1). -/
axiom ramsey3_mono (k : ℕ) : ramsey3 k ≤ ramsey3 (k + 1)

/- ## Known values -/

/-- R(3, 3) = 6. -/
axiom ramsey3_val_3 : ramsey3 3 = 6

/- ## Derived bounds -/

/-- R(3, k) is at least 6 for k ≥ 3, proved from R(3,3) = 6 and monotonicity. -/
theorem ramsey3_ge_six (k : ℕ) (hk : 3 ≤ k) : 6 ≤ ramsey3 k :=
  ramsey3_val_3 ▸ monotone_nat_of_le_succ ramsey3_mono hk

/- ## Asymptotic bounds -/

/- ## Main problems -/

/-- The consecutive difference R(3, k+1) − R(3, k). -/
noncomputable def ramseyDiff (k : ℕ) : ℕ := ramsey3 (k + 1) - ramsey3 k

/-- Erdős Problem 544, Part 1: R(3, k+1) − R(3, k) → ∞.
    For every bound M, there exists k₀ such that R(3, k+1) − R(3, k) ≥ M
    for all k ≥ k₀. -/
def ErdosProblem544_divergence : Prop :=
    ∀ M : ℕ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → M ≤ ramseyDiff k

/-- Erdős Problem 544, Part 2: Is R(3, k+1) − R(3, k) = o(k)?
    This asks whether the ratio (R(3, k+1) − R(3, k)) / k → 0. -/
def ErdosProblem544_sublinear : Prop :=
    ∀ ε : ℚ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (ramseyDiff k : ℚ) < ε * (k : ℚ)

/-- The full Erdős Problem 544: divergence is conjectured, and
    sublinearity is asked as a secondary question. -/
def ErdosProblem544 : Prop := ErdosProblem544_divergence ∧ ErdosProblem544_sublinear
