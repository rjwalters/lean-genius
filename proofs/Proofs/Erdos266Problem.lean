/-
  Erdős Problem #266: Shifted Sums and Irrationality

  **Conjecture (Stolarsky)**: Let aₙ be a sequence of positive integers with
  ∑ 1/aₙ convergent. Then there exists some integer t ≥ 1 such that
  ∑ 1/(aₙ + t) is irrational.

  **Answer**: FALSE — disproved by Kovač and Tao (2024)

  **Stronger Result**: There exists a strictly increasing sequence aₙ such that
  ∑ 1/(aₙ + t) is RATIONAL for ALL t ∈ ℚ (where t ≠ -aₙ for any n).

  This is a remarkable counterexample: a sequence where no shift can produce
  irrationality, and indeed all rational shifts produce rational sums.

  Reference: https://erdosproblems.com/266
  Key paper: Kovač, V. and Tao, T. "On several irrationality problems for Ahmes series."
             arXiv:2406.17593 (2024)
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries

namespace Erdos266

open Set Filter BigOperators

/- ## The Conjecture -/

/--
**Stolarsky's Conjecture**: For any sequence aₙ of positive integers with
convergent ∑ 1/aₙ, there should exist some integer t ≥ 1 making ∑ 1/(aₙ + t) irrational.

The intuition was: shifting by different integers should eventually "break"
any rationality pattern. But Kovač-Tao showed this intuition is wrong.
-/
def StolarskyConjecture : Prop :=
  ∀ a : ℕ → ℕ,
    (∀ n, 1 ≤ a n) →
    Summable (fun n => (1 : ℝ) / a n) →
    ∃ t : ℕ, 1 ≤ t ∧ Irrational (∑' n, (1 : ℝ) / (a n + t))

/- ## Main Result -/

/--
**Kovač-Tao (2024)**: Stolarsky's conjecture is FALSE.

There exists a sequence aₙ such that ∑ 1/(aₙ + t) is rational for ALL
integers t ≥ 1. No integer shift can produce irrationality.
-/
axiom stolarsky_conjecture_false : ¬StolarskyConjecture

/-- Erdős Problem #266: The conjecture is disproved -/
theorem erdos_266 : ¬StolarskyConjecture := stolarsky_conjecture_false

/- ## The Stronger Result -/

/--
**Kovač-Tao Stronger Result**: There exists a strictly increasing sequence aₙ
of positive integers such that ∑ 1/(aₙ + t) converges to a RATIONAL number
for ALL rational t (as long as t ≠ -aₙ for any n).

This is much stronger than just integers: ALL rational shifts give rational sums!
-/
axiom kovac_tao_all_rationals :
    ∃ a : ℕ → ℕ,
      StrictMono a ∧
      (∀ n, 1 ≤ a n) ∧
      ∀ t : ℚ,
        (∀ n, (t : ℝ) ≠ -(a n : ℝ)) →
        ∃ q : ℚ, ∑' n, (1 : ℝ) / ((a n : ℝ) + t) = q

/- ## Understanding the Counterexample -/

/-
The Kovač-Tao counterexample sequence is constructed carefully so that:
1. The sum ∑ 1/aₙ converges (terms decay fast enough)
2. For any shift t, the sum ∑ 1/(aₙ + t) telescopes or simplifies to a rational

The construction uses deep techniques from the theory of Ahmes series
(Egyptian fractions) and requires careful analysis of how shifts interact
with the sequence structure.
-/

/- ## Relation to Other Problems -/

/-
This problem is closely related to Erdős #264 (irrationality sequences).
Both ask about the "robustness" of irrationality under perturbations:

- Problem #264: Can bounded additive perturbations bₙ preserve irrationality?
- Problem #266: Can constant shifts t produce irrationality?

Kovač-Tao's unified approach resolved both negatively:
- #264: 2ⁿ is NOT an irrationality sequence
- #266: There exist sequences where NO shift produces irrationality
-/

/- ## Examples -/

/-- For illustration, harmonic-like sums ∑ 1/n diverge, so don't apply here -/
theorem harmonic_diverges : ¬Summable (fun n : ℕ => (1 : ℝ) / (n + 1)) := by
  -- The p-series ∑ 1/n^p diverges for p ≤ 1. Here p = 1.
  intro h
  have h1 : Summable (fun n : ℕ => (↑(n + 1) : ℝ)⁻¹) := by
    simp_rw [one_div] at h; exact h
  -- Summability of f ∘ (· + 1) implies summability of f (adding one term)
  have h2 : Summable (fun n : ℕ => ((n : ℝ))⁻¹) := by
    rw [summable_nat_add_iff 1] at h1 ⊢
    convert h1 using 1
    ext n; push_cast; ring_nf
  exact Real.not_summable_nat_of_tendsto_nat tendsto_harmonic h2

/-- Sums like ∑ 1/n² converge, so are candidates for Stolarsky's conjecture -/
theorem sum_reciprocal_squares_summable : Summable (fun n : ℕ => (1 : ℝ) / (n + 1)^2) := by
  -- The p-series ∑ 1/n^p converges for p > 1. Here p = 2.
  have h : Summable (fun n : ℕ => ((n : ℝ))⁻¹ ^ 2) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)).congr (fun n => by
      simp [inv_pow])
  rw [summable_nat_add_iff 1] at h ⊢
  apply h.of_nonneg_of_le (fun n => by positivity) (fun n => by positivity)
  intro n
  simp only [one_div, inv_pow]
  apply inv_le_inv_of_le (by positivity : (0 : ℝ) < (↑(n + 1))^2)
  push_cast; nlinarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n]

/-- The geometric series ∑ 1/2ⁿ converges to 2 -/
example : ∑' n : ℕ, (1 : ℝ) / 2^n = 2 := by
  have : (fun n : ℕ => (1 : ℝ) / 2 ^ n) = (fun n : ℕ => ((1 : ℝ) / 2) ^ n) := by
    ext n; rw [one_div, one_div, inv_pow]
  rw [this, tsum_geometric_of_lt_one (by positivity) (by norm_num : (1:ℝ)/2 < 1)]
  norm_num

/-- Shifted geometric: ∑ 1/(2ⁿ + 1) also converges -/
example : Summable (fun n : ℕ => (1 : ℝ) / (2^n + 1)) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity)
  · intro n
    rw [one_div]
    exact inv_le_inv_of_le (by positivity : (0:ℝ) < 2^n)
      (le_add_of_nonneg_right (by positivity))
  · have : (fun n : ℕ => (1 : ℝ) / 2 ^ n) = (fun n : ℕ => ((1 : ℝ) / 2) ^ n) := by
      ext n; rw [one_div, one_div, inv_pow]
    rw [this]
    exact summable_geometric_of_lt_one (by positivity) (by norm_num : (1:ℝ)/2 < 1)

end Erdos266
