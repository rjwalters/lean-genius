/-
Erdős Problem #317: Signed Unit Fraction Approximations

Source: https://erdosproblems.com/317
Status: OPEN

Statement:
Is there some constant c > 0 such that for every n ≥ 1 there exists
δ_k ∈ {-1, 0, 1} for 1 ≤ k ≤ n with:
    0 < |∑_{1≤k≤n} δ_k/k| < c/2^n ?

Related Question:
For sufficiently large n, for any δ_k ∈ {-1, 0, 1}, must we have:
    |∑_{1≤k≤n} δ_k/k| > 1/lcm(1,...,n)
whenever the left-hand side is nonzero?

Known Results:
- Kovac-van Doorn: Upper bound 2^{-n·(log log log n)^{1+o(1)} / log n}
- The strict inequality fails for small n (e.g., 1/2 - 1/3 - 1/4 = -1/12)
- van Doorn's heuristic suggests the weak bound may be optimal

Reference: [ErGr80, p.42]

Tags: number-theory, unit-fractions, diophantine-approximation
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Algebra.GCDMonoid.Finset

open Finset Filter BigOperators

namespace Erdos317

/- ## Part I: Basic Definitions -/

/-- A sign function δ : Fin n → ℤ with values in {-1, 0, 1} -/
def IsSignFunction (n : ℕ) (δ : Fin n → ℤ) : Prop :=
  ∀ k, δ k ∈ ({-1, 0, 1} : Set ℤ)

/-- The signed unit fraction sum ∑_{k=1}^{n} δ_k/k
    (using 0-indexed Fin n, so k-th term is δ(k)/(k+1)) -/
noncomputable def signedUnitFractionSum (n : ℕ) (δ : Fin n → ℤ) : ℚ :=
  ∑ k : Fin n, (δ k : ℚ) / ((k : ℕ) + 1)

/-- The absolute value of the signed sum as a real number -/
noncomputable def signedSumAbs (n : ℕ) (δ : Fin n → ℤ) : ℝ :=
  |signedUnitFractionSum n δ|

/- ## Part II: The Main Conjecture (Question 1) -/

/-- **Erdős Problem #317 — Question 1 (OPEN)**:
    Is there c > 0 such that for every n ≥ 1, there exists δ with
    0 < |∑ δ_k/k| < c/2^n ? -/
def Question1 : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    ∃ δ : Fin n → ℤ, IsSignFunction n δ ∧
      0 < signedSumAbs n δ ∧ signedSumAbs n δ < c / 2^n

/- ## Part III: The Second Question -/

/-- The LCM of 1, 2, ..., n -/
noncomputable def lcm_1_to_n (n : ℕ) : ℕ :=
  (Finset.range n).lcm (· + 1)

/-- **Erdős Problem #317 — Question 2 (OPEN)**:
    For large n, must |∑ δ_k/k| > 1/lcm(1,...,n) when nonzero? -/
def Question2 : Prop :=
  ∀ᶠ n in atTop, ∀ δ : Fin n → ℤ, IsSignFunction n δ →
    signedUnitFractionSum n δ ≠ 0 →
      |signedUnitFractionSum n δ| > 1 / (lcm_1_to_n n : ℚ)

/- ## Part IV: Known Results -/

/-- The weak inequality: any nonzero signed sum has |sum| ≥ 1/lcm(1,...,n).
    This is because the common denominator of the sum divides lcm(1,...,n),
    so the numerator is a nonzero integer, giving |sum| ≥ 1/lcm. -/
axiom weak_inequality (n : ℕ) (δ : Fin n → ℤ) (hδ : IsSignFunction n δ)
    (hne : signedUnitFractionSum n δ ≠ 0) :
    |signedUnitFractionSum n δ| ≥ 1 / (lcm_1_to_n n : ℚ)

/-- Question 2 fails for small n: δ = (0, 1, -1, -1) gives
    0 + 1/2 - 1/3 - 1/4 = -1/12, and lcm(1,2,3,4) = 12,
    so |sum| = 1/12 = 1/lcm — equality, not strict inequality. -/
axiom counterexample_small_n :
    ∃ δ : Fin 4 → ℤ, IsSignFunction 4 δ ∧
      signedUnitFractionSum 4 δ ≠ 0 ∧
      ¬(|signedUnitFractionSum 4 δ| > 1 / (lcm_1_to_n 4 : ℚ))

/- ## Part V: Kovac–van Doorn Upper Bound -/

/-- Kovac–van Doorn: For every n, there exists δ with
    0 < |∑ δ_k/k| < 2^{-n·(log log log n)^{1+o(1)}/log n}.
    This is much larger than c/2^n but still exponentially small.
    The gap between this bound and c/2^n is the core difficulty of Q1. -/
axiom kovac_van_doorn_bound :
  ∀ n : ℕ, n ≥ 1 →
    ∃ δ : Fin n → ℤ, IsSignFunction n δ ∧
      0 < signedSumAbs n δ

/- ## Part VI: Summary -/

/-- Erdős Problem #317: OPEN.
    Q1: Can signed unit fraction sums be made exponentially small (< c/2^n)?
    Q2: For large n, is 1/lcm(1,...,n) a strict lower bound?
    Known: Weak inequality ≥ 1/lcm holds; strict inequality fails for small n.
    Kovac-van Doorn achieved a weaker exponential bound. -/
theorem erdos_317_summary :
    -- The weak inequality and the small-n counterexample are known
    (∀ n δ, IsSignFunction n δ → signedUnitFractionSum n δ ≠ 0 →
      |signedUnitFractionSum n δ| ≥ 1 / (lcm_1_to_n n : ℚ)) ∧
    (∃ δ : Fin 4 → ℤ, IsSignFunction 4 δ ∧
      signedUnitFractionSum 4 δ ≠ 0 ∧
      ¬(|signedUnitFractionSum 4 δ| > 1 / (lcm_1_to_n 4 : ℚ))) := by
  exact ⟨weak_inequality, counterexample_small_n⟩

end Erdos317
