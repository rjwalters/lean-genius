/-
  Aristotle targets for Erdős Problem #165: Asymptotic Formula for R(3,k)
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos165Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main problem (exact constant in R(3,k) ~ c·k²/log k)
  - NOT theorems depending on axiomatized Ramsey bounds (Shearer, HHKP)
  - Routine real number and logarithm facts used in asymptotic analysis
  - No definition sorries
  - No axioms

  Included targets (5):
  - log_pos_of_one_lt: 1 < x → 0 < Real.log x
  - sq_div_log_pos: k ≥ 2 → 0 < k^2 / Real.log k
  - mul_div_le_iff_le: basic real inequality rearrangement
  - le_max_left_of_le: a ≤ b → a ≤ max b c
  - nat_cast_pos: 0 < (n : ℝ) ↔ 0 < n
-/
import Mathlib

open Real

namespace Erdos165Aristotle

-- Routine: log is positive for inputs > 1.
-- Real.log x > 0 when x > 1.
theorem log_pos_of_one_lt (x : ℝ) (hx : 1 < x) : 0 < Real.log x := by
  sorry

-- Routine: k²/(log k) is positive for k ≥ 2.
-- Both k² and log k are positive when k ≥ 2.
theorem sq_div_log_pos (k : ℕ) (hk : 2 ≤ k) : 0 < (k : ℝ)^2 / Real.log k := by
  sorry

-- Routine: c₁ * k²/log k ≤ c₂ * k²/log k when c₁ ≤ c₂ and k ≥ 2.
-- Just multiplying through by k²/log k.
theorem ramsey_bound_mono (c₁ c₂ : ℝ) (k : ℕ) (hk : 2 ≤ k) (hc : c₁ ≤ c₂) :
    c₁ * (k : ℝ)^2 / Real.log k ≤ c₂ * (k : ℝ)^2 / Real.log k := by
  sorry

-- Routine: if a ≤ b and c ≤ d then a + c ≤ b + d.
-- Standard add_le_add.
theorem sum_le_sum (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  sorry

-- Routine: (k : ℝ) ≥ 0 for any natural k.
-- Natural number casts are nonneg.
theorem nat_cast_nonneg' (k : ℕ) : (0 : ℝ) ≤ (k : ℝ) := by
  sorry

end Erdos165Aristotle
