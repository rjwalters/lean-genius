/-
  Aristotle targets for Erdős Problem #627
  Routine supporting lemmas for automated proof search.
  See Erdos627Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open question (limit existence of f(n)/(n/(log n)²))
  - NOT theorems depending on def-sorries (f, ramseyNumber, mycielskiGraph, kneserGraph)
  - Routine supporting facts: numerical bounds on log 2, coefficient positivity, chi/omega basics
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos627Aristotle

open Real

/-- The lower bound constant (log 2)²/4 for the potential limit. -/
noncomputable def limitLowerBound : ℝ := (Real.log 2)^2 / 4

/-- The upper bound constant (log 2)² for the potential limit. -/
noncomputable def limitUpperBound : ℝ := (Real.log 2)^2

/-- The lower coefficient in Kostochka's bound: 1/(4 log k). -/
noncomputable def lowerCoeff (k : ℕ) : ℝ := 1 / (4 * Real.log k)

/-- The upper coefficient in Erdős's bound: 2/log(k-2). -/
noncomputable def upperCoeff (k : ℕ) : ℝ := 2 / Real.log (k - 2)

-- Routine: log 2 > 0.
-- 2 > 1, so log 2 > 0 by Real.log_pos.
theorem log2_pos : Real.log 2 > 0 :=
  Real.log_pos (by norm_num)

-- Routine: (log 2)² > 0.
-- log 2 > 0 since 2 > 1, so its square is positive.
theorem log2_sq_pos : (Real.log 2)^2 > 0 :=
  pow_pos log2_pos 2

-- Routine: limitLowerBound > 0.
-- (log 2)²/4 > 0 since (log 2)² > 0 and 4 > 0.
theorem limitLowerBound_pos : limitLowerBound > 0 := by
  simp only [limitLowerBound]
  exact div_pos log2_sq_pos (by norm_num)

-- Routine: limitUpperBound > 0.
-- (log 2)² > 0 directly.
theorem limitUpperBound_pos : limitUpperBound > 0 := by
  simp only [limitUpperBound]
  exact log2_sq_pos

-- Routine: limitLowerBound < limitUpperBound.
-- (log 2)²/4 < (log 2)²  iff  1/4 < 1  (dividing both sides by (log 2)² > 0).
theorem limit_bounds_numerical : limitLowerBound < limitUpperBound := by
  simp only [limitLowerBound, limitUpperBound]
  have h := log2_sq_pos
  linarith

-- Routine: For k ≥ 4, log k > 0.
-- k ≥ 4 > 1, so log k > 0 by Real.log_pos.
theorem log_k_pos (k : ℕ) (hk : k ≥ 4) : Real.log k > 0 := by
  apply Real.log_pos
  have : (1 : ℕ) < k := by omega
  exact_mod_cast this

-- Routine: For k ≥ 4, log(k - 2) > 0.
-- k ≥ 4 implies k - 2 ≥ 2 > 1, so log(k-2) > 0.
theorem log_k_minus_2_pos (k : ℕ) (hk : k ≥ 4) : Real.log ((k : ℝ) - 2) > 0 := by
  apply Real.log_pos
  have : (4 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

-- Routine: 4 * Real.log k > 0 for k ≥ 4.
-- Product of two positive reals: 4 > 0 and log k > 0.
theorem four_mul_log_pos (k : ℕ) (hk : k ≥ 4) : 4 * Real.log k > 0 :=
  mul_pos (by norm_num) (log_k_pos k hk)

-- Routine: For k ≥ 4, lowerCoeff k > 0.
-- 1/(4 * log k) > 0 since log k > 0 and 4 > 0.
theorem lowerCoeff_pos (k : ℕ) (hk : k ≥ 4) : lowerCoeff k > 0 := by
  simp only [lowerCoeff]
  exact div_pos (by norm_num) (four_mul_log_pos k hk)

-- Routine: For k ≥ 4, upperCoeff k > 0.
-- 2/log(k-2) > 0 since log(k-2) > 0.
theorem upperCoeff_pos (k : ℕ) (hk : k ≥ 4) : upperCoeff k > 0 := by
  simp only [upperCoeff]
  apply div_pos (by norm_num)
  have h2k : 2 ≤ k := by omega
  rw [Nat.cast_sub h2k]
  exact log_k_minus_2_pos k hk

-- Routine: For k ≥ 4, lowerCoeff k ≤ upperCoeff k.
-- 1/(4 log k) ≤ 2/log(k-2) since log(k-2) ≤ log k and 1/4 ≤ 2.
theorem lowerCoeff_le_upperCoeff (k : ℕ) (hk : k ≥ 4) :
    lowerCoeff k ≤ upperCoeff k := by
  simp only [lowerCoeff, upperCoeff]
  have h2k : 2 ≤ k := by omega
  rw [Nat.cast_sub h2k]
  have hlogk := log_k_pos k hk
  have hlogk2 := log_k_minus_2_pos k hk
  rw [div_le_div_iff (mul_pos (by norm_num : (0:ℝ) < 4) hlogk) hlogk2]
  have hk_cast : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog_mono : Real.log ((k : ℝ) - 2) ≤ Real.log k :=
    Real.log_le_log (by linarith) (by linarith)
  linarith

-- Routine: For k ≥ 4 and n ≥ 2, n^(1:ℝ) = n.
-- Real.rpow with exponent 1 equals the base (as a real number cast).
theorem rpow_one_cast (n : ℕ) (hn : n ≥ 2) : (n : ℝ)^(1 : ℝ) = n :=
  Real.rpow_one n

end Erdos627Aristotle
