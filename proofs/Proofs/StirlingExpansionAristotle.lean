/-
  Aristotle targets for StirlingExpansion
  Higher-order Stirling expansion terms for automated proof search.
  See StirlingExpansion.lean for the main formalization.

  Status: all three targets below are now discharged.
  - `stirling_step_formula` is proved here directly (self-contained log arithmetic).
  - `stirling_first_correction` and `stirling_two_term_expansion` are the public
    results established in `Proofs.StirlingExpansion`; here we re-expose them so the
    companion file is sorry-free and the named targets resolve to machine-checked proofs.

  Criteria for inclusion:
  - Well-known asymptotic analysis results
  - Stirling first correction and two-term expansion
  - Clean theorem statements with no definition sorries
  - No axioms, no open conjectures
-/
import Proofs.StirlingExpansion
import Mathlib.Tactic

namespace StirlingExpansionAristotle

open Stirling Real Filter

/-- The Stirling step formula: log(stirlingSeq k) - log(stirlingSeq(k+1)) = (k+1/2)*log(1+1/k) - 1.

    Proof sketch: unfold stirlingSeq(n) = n!/(sqrt(2n)*(n/e)^n) and compute:
      log(stirlingSeq k / stirlingSeq(k+1))
      = (k+1/2)*log((k+1)/k) - 1
      = (k+1/2)*log(1+1/k) - 1

    Uses: Real.log_div, Real.log_mul, Real.log_pow, Real.log_sqrt, Real.log_exp,
          Nat.factorial_succ
-/
theorem stirling_step_formula (k : ℕ) (hk : 1 ≤ k) :
    Real.log (stirlingSeq k) - Real.log (stirlingSeq (k + 1)) =
    ((k : ℝ) + 1 / 2) * Real.log (1 + 1 / (k : ℝ)) - 1 := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
  have hk1_ne : (k : ℝ) + 1 ≠ 0 := hk1_pos.ne'
  have hsqrt_k : 0 < Real.sqrt (2 * (k : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hsqrt_k1 : 0 < Real.sqrt (2 * ((k : ℝ) + 1)) := Real.sqrt_pos.mpr (by positivity)
  have hpow_k : 0 < ((k : ℝ) / Real.exp 1) ^ k :=
    pow_pos (div_pos hk_pos (Real.exp_pos 1)) k
  have hpow_k1 : 0 < (((k : ℝ) + 1) / Real.exp 1) ^ (k + 1) :=
    pow_pos (div_pos hk1_pos (Real.exp_pos 1)) (k + 1)
  -- log(stirlingSeq k) = log(k!) - (1/2)·log(2k) - k·(log k - 1)
  have hlog_k : Real.log (stirlingSeq k) =
      Real.log (k.factorial : ℝ) - (1/2 : ℝ) * Real.log (2 * (k : ℝ)) -
      (k : ℝ) * (Real.log (k : ℝ) - 1) := by
    rw [show stirlingSeq k = (k.factorial : ℝ) /
          (Real.sqrt (2 * ↑k) * (↑k / Real.exp 1) ^ k) from rfl]
    rw [Real.log_div (Nat.cast_pos.mpr (Nat.factorial_pos k)).ne'
                     (mul_pos hsqrt_k hpow_k).ne']
    rw [Real.log_mul hsqrt_k.ne' hpow_k.ne']
    rw [Real.log_sqrt (by positivity : (0 : ℝ) ≤ 2 * ↑k)]
    rw [Real.log_pow]
    rw [Real.log_div hk_ne (Real.exp_pos 1).ne']
    rw [Real.log_exp]
    push_cast; ring
  -- log(stirlingSeq(k+1)) = log((k+1)!) - (1/2)·log(2(k+1)) - (k+1)·(log(k+1) - 1)
  have hlog_k1 : Real.log (stirlingSeq (k + 1)) =
      Real.log ((k + 1).factorial : ℝ) - (1/2 : ℝ) * Real.log (2 * ((k : ℝ) + 1)) -
      ((k : ℝ) + 1) * (Real.log ((k : ℝ) + 1) - 1) := by
    rw [show stirlingSeq (k + 1) = ((k + 1).factorial : ℝ) /
          (Real.sqrt (2 * ↑(k + 1)) * (↑(k + 1) / Real.exp 1) ^ (k + 1)) from rfl]
    have h_cast : (↑(k + 1) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [h_cast]
    rw [Real.log_div (Nat.cast_pos.mpr (Nat.factorial_pos (k + 1))).ne'
                     (mul_pos hsqrt_k1 hpow_k1).ne']
    rw [Real.log_mul hsqrt_k1.ne' hpow_k1.ne']
    rw [Real.log_sqrt (by positivity : (0 : ℝ) ≤ 2 * ((k : ℝ) + 1))]
    rw [Real.log_pow]
    rw [Real.log_div hk1_ne (Real.exp_pos 1).ne']
    rw [Real.log_exp]
    push_cast; ring
  -- log((k+1)!) = log(k!) + log(k+1)
  have hfact_step : Real.log ((k + 1).factorial : ℝ) =
      Real.log (k.factorial : ℝ) + Real.log ((k : ℝ) + 1) := by
    have heq : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [heq, Real.log_mul hk1_ne (Nat.cast_pos.mpr (Nat.factorial_pos k)).ne']
    ring
  -- log(1 + 1/k) = log(k+1) - log(k)
  have hlog_rhs : Real.log (1 + 1 / (k : ℝ)) = Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) := by
    rw [show (1 : ℝ) + 1 / (k : ℝ) = ((k : ℝ) + 1) / (k : ℝ) by field_simp]
    rw [Real.log_div hk1_ne hk_ne]
  -- log(2k) = log 2 + log k,  log(2(k+1)) = log 2 + log(k+1)
  have hlog_2k : Real.log (2 * (k : ℝ)) = Real.log 2 + Real.log (k : ℝ) :=
    Real.log_mul (by norm_num) hk_ne
  have hlog_2k1 : Real.log (2 * ((k : ℝ) + 1)) = Real.log 2 + Real.log ((k : ℝ) + 1) :=
    Real.log_mul (by norm_num) hk1_ne
  rw [hlog_k, hlog_k1, hfact_step, hlog_rhs, hlog_2k, hlog_2k1]
  push_cast; ring

/-- Stirling's First Correction:
    stirlingSeq(n)/√π = 1 + 1/(12n) + O(1/n²).
    Machine-checked in `Proofs.StirlingExpansion`. -/
theorem stirling_first_correction :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
      |stirlingSeq n / Real.sqrt π - (1 + 1 / (12 * (n : ℝ)))| ≤ C / (n : ℝ) ^ 2 :=
  StirlingExpansion.stirling_first_correction

/-- Stirling Two-Term Expansion:
    n! = √(2πn)·(n/e)^n · (1 + 1/(12n) + O(1/n²)).
    Machine-checked in `Proofs.StirlingExpansion`. -/
theorem stirling_two_term_expansion :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
      |(n.factorial : ℝ) / (Real.sqrt (2 * π * n) * ((n : ℝ) / Real.exp 1) ^ n) -
        (1 + 1 / (12 * (n : ℝ)))| ≤ C / (n : ℝ) ^ 2 :=
  StirlingExpansion.stirling_two_term_expansion

end StirlingExpansionAristotle
