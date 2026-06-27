/-
  Erdős #671 — Orphan worktree for the single tractable supporting estimate.

  UNREGISTERED: this file is NOT part of the gallery entry. It exists only to
  develop / Aristotle-verify the one self-contained sorry of
  `Proofs/Erdos671Problem.lean`, namely `equidistant_diverges`, in isolation
  before any integration into the registered file.

  The registered theorem is
    `lebesgueConstant (equidistantNodes n hn) ≥ 2^(n-1) / n^2`.
  Since `lebesgueConstant = ⨆ x ∈ [-1,1], lebesgueFunction x`, a lower bound at
  any single admissible point x* dominates the constant (that sup-step needs
  `BddAbove`, handled separately). The mathematical heart is the *pointwise*
  estimate isolated here at x* = -1 + 1/(n-1), the midpoint of the first
  subinterval. This file carries no analysis — only a finite product/factorial
  inequality — and is the right target for `prove_file`.

  Reference numerics (research/problems/erdos-671/verify-equidistant-bound.py):
  the bound holds for all n = 2..25, with the dominant Lagrange basis index near
  the centre i ≈ (n-2)/2 (NOT an endpoint index).
-/

import Mathlib

namespace Erdos671Orphan

open Polynomial

/-- Points for interpolation: a_i^n ∈ [-1, 1]. -/
structure InterpolationPoints (n : ℕ) where
  points : Fin n → ℝ
  in_interval : ∀ i, points i ∈ Set.Icc (-1 : ℝ) 1
  distinct : ∀ i j, i ≠ j → points i ≠ points j

/-- The Lagrange basis polynomial p_i^n. -/
noncomputable def lagrangeBasis {n : ℕ} (pts : InterpolationPoints n) (i : Fin n) :
    Polynomial ℝ :=
  ∏ j ∈ (Finset.univ : Finset (Fin n)).filter (fun k => k ≠ i),
    (Polynomial.C (1 / (pts.points i - pts.points j)) *
     (Polynomial.X - Polynomial.C (pts.points j)) : Polynomial ℝ)

/-- The Lebesgue function λ_n(x) = Σ |p_i^n(x)|. -/
noncomputable def lebesgueFunction {n : ℕ} (pts : InterpolationPoints n) (x : ℝ) : ℝ :=
  ∑ i : Fin n, |(lagrangeBasis pts i).eval x|

/-- Equidistant nodes: x_k = -1 + 2k/(n-1). -/
noncomputable def equidistantNodes (n : ℕ) (hn : n ≥ 2) : InterpolationPoints n where
  points := fun k => -1 + 2 * (k.val : ℝ) / ((n : ℝ) - 1)
  in_interval := by
    intro k
    have hn_cast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hn
    have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    simp only [Set.mem_Icc]
    constructor
    · have : (0 : ℝ) ≤ 2 * (k.val : ℝ) / ((n : ℝ) - 1) :=
        div_nonneg (by positivity) (le_of_lt hn1_pos)
      linarith
    · have hklt : (k.val : ℝ) < (n : ℝ) := by exact_mod_cast k.isLt
      have : 2 * (k.val : ℝ) / ((n : ℝ) - 1) ≤ 2 := by
        rw [div_le_iff hn1_pos]; linarith
      linarith
  distinct := by
    intro k j hkj heq
    apply hkj
    have hn_cast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hn
    have hn1_ne : (n : ℝ) - 1 ≠ 0 := by linarith
    have h1 : 2 * (k.val : ℝ) / ((n : ℝ) - 1) = 2 * (j.val : ℝ) / ((n : ℝ) - 1) := by
      linarith
    have h2 : (k.val : ℝ) = j.val := by field_simp [hn1_ne] at h1; linarith
    exact Fin.ext (by exact_mod_cast h2)

/-- The evaluation point: midpoint of the first subinterval, x* = -1 + 1/(n-1). -/
noncomputable def midPoint (n : ℕ) : ℝ := -1 + 1 / ((n : ℝ) - 1)

/-- x* lies in [-1, 1] for n ≥ 2. -/
theorem midPoint_mem (n : ℕ) (hn : n ≥ 2) :
    midPoint n ∈ Set.Icc (-1 : ℝ) 1 := by
  have hn_cast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  unfold midPoint
  simp only [Set.mem_Icc]
  constructor
  · have : (0 : ℝ) ≤ 1 / ((n : ℝ) - 1) := by positivity
    linarith
  · have : 1 / ((n : ℝ) - 1) ≤ 1 := by
      rw [div_le_one hn1_pos]; linarith
    linarith

/--
  POINTWISE LEBESGUE LOWER BOUND (the mathematical heart of `equidistant_diverges`).

  At the midpoint x* = -1 + 1/(n-1) of the first equidistant subinterval, the
  Lebesgue function already exceeds 2^(n-1)/n^2. This is a finite product /
  factorial inequality (no analysis, no supremum): for each basis index i,
    |p_i(x*)| = (∏_{k≠i}|2k-1|) / (2^(n-1) · ∏_{k≠i}|i-k|),
  and the central index i ≈ (n-2)/2 contributes a term ≥ 2^(n-1)/n^2.

  Verified numerically for n = 2..25 (verify-equidistant-bound.py).
-/
theorem lebesgueFunction_midPoint_ge (n : ℕ) (hn : n ≥ 2) :
    lebesgueFunction (equidistantNodes n hn) (midPoint n) ≥ 2 ^ (n - 1) / (n : ℝ) ^ 2 := by
  sorry

end Erdos671Orphan
