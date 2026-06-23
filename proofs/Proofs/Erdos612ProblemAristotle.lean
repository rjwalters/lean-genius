/-
  Aristotle targets for Erdős Problem #612: Diameter Bounds for Clique-Free Graphs
  Routine supporting lemmas for automated proof search.
  See Erdos612Problem.lean for the main formalization.

  Focus: Analytic and algebraic properties of the amended diameter coefficient
  function amended_alpha(k) = 3 - 2/k for K_{k+1}-free graphs.
-/

import Mathlib

namespace Erdos612

/-- The amended coefficient: (3 - 2/k) for K_{k+1}-free -/
def amended_alpha (k : ℕ) : ℝ :=
  3 - 2 / k

/-- As k → ∞, the coefficient (3 - 2/k) tends to 3 -/
theorem amended_limit :
    Filter.Tendsto (fun k : ℕ => amended_alpha k) Filter.atTop (nhds 3) := by
  unfold amended_alpha
  have h : Filter.Tendsto (fun k : ℕ => (2 : ℝ) / k) Filter.atTop (nhds 0) := by
    simp_rw [div_eq_mul_inv]
    apply Filter.Tendsto.const_mul_zero
    exact tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have h3 : Filter.Tendsto (fun k : ℕ => (3 : ℝ) - 2 / k) Filter.atTop (nhds (3 - 0)) :=
    h.const_sub 3
  simp only [sub_zero] at h3
  exact h3

/-- The coefficient is positive for k ≥ 2 -/
theorem amended_alpha_pos (k : ℕ) (hk : k ≥ 2) : 0 < amended_alpha k := by
  unfold amended_alpha
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have h2k : 2 / (k : ℝ) ≤ 1 := by
    rw [div_le_one hk_pos]
    exact_mod_cast hk
  linarith

/-- The coefficient is strictly less than 3 for k ≥ 1 -/
theorem amended_alpha_lt_three (k : ℕ) (hk : k ≥ 1) : amended_alpha k < 3 := by
  unfold amended_alpha
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have h2k : 0 < 2 / (k : ℝ) := by positivity
  linarith

/-- The coefficient is monotone increasing -/
theorem amended_alpha_mono (k₁ k₂ : ℕ) (hk₁ : k₁ ≥ 1) (h : k₁ ≤ k₂) :
    amended_alpha k₁ ≤ amended_alpha k₂ := by
  unfold amended_alpha
  apply sub_le_sub_left
  apply div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero (by omega))
  exact_mod_cast h

end Erdos612
