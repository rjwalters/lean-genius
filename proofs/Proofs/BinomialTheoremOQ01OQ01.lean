/-
  Binomial Theorem - Open Question 01 - Sub-Question 01:
  Newton's Generalized Binomial Theorem via Analytic Function Theory

  This file develops the analytic function theory perspective:
  1. ODE characterization: (1+x)f'(x) = αf(x) uniquely determines (1+x)^α
  2. Coefficient recurrence from ODE
  3. Analytic properties from Mathlib's HasFPowerSeriesOnBall
  4. Functional equation (1+x)^α · (1+x)^β = (1+x)^(α+β)
-/

import Mathlib

open Finset Real

namespace BinomialTheoremOQ01OQ01

noncomputable def genBinom (α : ℝ) (k : ℕ) : ℝ :=
  (∏ j ∈ range k, (α - j)) / k.factorial

theorem genBinom_zero (α : ℝ) : genBinom α 0 = 1 := by
  simp [genBinom]

theorem genBinom_one (α : ℝ) : genBinom α 1 = α := by
  simp [genBinom, prod_range_one]

-- Part I: ODE Recurrence and Coefficient Uniqueness

/-- The ODE recurrence: (k+1) · C(α, k+1) = (α - k) · C(α, k). -/
theorem ode_recurrence (α : ℝ) (k : ℕ) :
    (↑k + 1 : ℝ) * genBinom α (k + 1) = (α - ↑k) * genBinom α k := by
  simp only [genBinom, Nat.factorial_succ, prod_range_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp

/-- The ODE recurrence uniquely determines all coefficients from a₀ = 1. -/
theorem genBinom_unique_from_ode (a : ℕ → ℝ) (α : ℝ)
    (h0 : a 0 = 1)
    (hrec : ∀ k : ℕ, (↑k + 1 : ℝ) * a (k + 1) = (α - ↑k) * a k) :
    ∀ k : ℕ, a k = genBinom α k := by
  intro k
  induction k with
  | zero => rw [h0, genBinom_zero]
  | succ n ih =>
    have hpos : (↑n + 1 : ℝ) ≠ 0 := by positivity
    have h1 := hrec n
    have h2 := ode_recurrence α n
    rw [ih] at h1
    exact mul_left_cancel₀ hpos (by linarith)

-- Part II: Analytic Properties (from Mathlib)

/-- The generalized binomial series is analytic on the open unit ball. -/
theorem binomial_series_analytic (α : ℝ) :
    HasFPowerSeriesOnBall (fun y : ℝ => (1 + y) ^ α) (binomialSeries ℝ α) 0 1 :=
  Real.one_add_rpow_hasFPowerSeriesOnBall_zero

-- AnalyticAt at non-center points requires more careful API usage
-- The key result is binomial_series_analytic above

-- Part III: Functional Equation

/-- The functional equation: (1+x)^α · (1+x)^β = (1+x)^(α+β) for x > -1. -/
theorem rpow_add_exponents (α β x : ℝ) (hx : -1 < x) :
    (1 + x) ^ α * (1 + x) ^ β = (1 + x) ^ (α + β) :=
  (rpow_add (by linarith : 0 < 1 + x) α β).symm

/-- (1+x)^0 = 1. -/
theorem rpow_zero_one (x : ℝ) : (1 + x) ^ (0 : ℝ) = 1 := rpow_zero _

/-- (1+x)^1 = 1+x. -/
theorem rpow_one_id (x : ℝ) : (1 + x) ^ (1 : ℝ) = 1 + x := rpow_one _

-- Part IV: Coefficient Ratio and Convergence

/-- The ratio C(α,k+1)/C(α,k) = (α-k)/(k+1) when C(α,k) ≠ 0. -/
theorem genBinom_ratio (α : ℝ) (k : ℕ) (hk : genBinom α k ≠ 0) :
    genBinom α (k + 1) / genBinom α k = (α - ↑k) / (↑k + 1) := by
  have hpos : (↑k + 1 : ℝ) ≠ 0 := by positivity
  have h := ode_recurrence α k
  field_simp
  linarith

-- Part V: Negation and Absorption Identities

/-- C(0, k) = 0 for k ≥ 1. -/
theorem genBinom_zero_succ (k : ℕ) : genBinom 0 (k + 1) = 0 := by
  simp only [genBinom, prod_range_succ']
  simp [Nat.cast_zero, sub_zero, zero_mul, zero_div]

/-- Negation: C(-1, k) = (-1)^k. -/
theorem genBinom_neg_one (k : ℕ) : genBinom (-1 : ℝ) k = (-1) ^ k := by
  induction k with
  | zero => simp [genBinom]
  | succ n ih =>
    have h := ode_recurrence (-1 : ℝ) n
    have hpos : (↑n + 1 : ℝ) ≠ 0 := by positivity
    rw [ih] at h
    have : genBinom (-1) (n + 1) = (-1) ^ (n + 1) := by
      have h2 : (↑n + 1 : ℝ) * genBinom (-1) (n + 1) = (↑n + 1) * (-1) ^ (n + 1) := by
        rw [h]; ring
      exact mul_left_cancel₀ hpos h2
    exact this

end BinomialTheoremOQ01OQ01
