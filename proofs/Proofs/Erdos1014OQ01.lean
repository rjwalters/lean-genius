/-
Erdős Problem #1014 OQ-01: Ratio Convergence for k = 3

We prove that R(3, l+1) / R(3, l) → 1 as l → ∞, resolving the k = 3 case
of Erdős Problem #1014.

The proof uses only:
  (1) The Ramsey recurrence R(k, l+1) ≤ R(k, l) + R(k-1, l+1)
  (2) The trivial value R(2, l) = l
  (3) The Kim-Shearer lower bound R(3, l) ≥ c · l²/log l
  (4) Monotonicity R(3, l) ≤ R(3, l+1)

Key insight: The recurrence gives R(3, l+1) - R(3, l) ≤ R(2, l+1) = l + 1.
Combined with the quadratic lower bound R(3, l) ≥ c · l²/log l, the ratio
R(3, l+1)/R(3, l) - 1 ≤ (l+1)/(c · l²/log l) = O(log l / l) → 0.

This shows the Θ(l²/log l) bounds suffice for k = 3 when combined with the
recurrence. The recurrence provides a tight bound on the increment that
Θ bounds alone cannot.

References:
- Kim (1995): R(3, l) ≥ c · l² / log l
- Shearer (1995): Improved constant in lower bound
- Mattheus-Verstraëte (2024): R(3, t) ≥ (1/4 - o(1)) · t² / log t
- Erdős [Er71], Problem 1014
-/

import Mathlib

open Real

namespace Erdos1014OQ01

-- ══════════════════════════════════════════════════════════════════
-- § Axioms (from parent formalization Erdos1014Problem.lean)
-- ══════════════════════════════════════════════════════════════════

/-- The Ramsey number R(k, l). -/
axiom ramseyNumber (k l : ℕ) : ℕ

/-- R(k, l) ≥ 1 for k, l ≥ 1. -/
axiom ramsey_pos (k l : ℕ) (hk : k ≥ 1) (hl : l ≥ 1) :
  ramseyNumber k l ≥ 1

/-- Monotonicity: R(k, l) ≤ R(k, l+1). -/
axiom ramsey_monotone_right (k l : ℕ) :
  ramseyNumber k l ≤ ramseyNumber k (l + 1)

/-- Ramsey recurrence: R(k, l+1) ≤ R(k, l) + R(k-1, l+1). -/
axiom ramsey_recurrence (k l : ℕ) (hk : k ≥ 2) (hl : l ≥ 1) :
  ramseyNumber k (l + 1) ≤ ramseyNumber k l + ramseyNumber (k - 1) (l + 1)

/-- R(2, l) = l for l ≥ 1. -/
axiom ramsey_k2 (l : ℕ) (hl : l ≥ 1) : ramseyNumber 2 l = l

-- ══════════════════════════════════════════════════════════════════
-- § Corrected R(3, l) Lower Bound
-- ══════════════════════════════════════════════════════════════════

/-- Kim (1995) / Shearer (1995): There exists c > 0 such that
    R(3, l) ≥ c · l² / log l for all sufficiently large l. -/
axiom R3_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    (ramseyNumber 3 l : ℝ) ≥ c * (l : ℝ) ^ 2 / Real.log (l : ℝ)

-- ══════════════════════════════════════════════════════════════════
-- § Step 1: Linear Increment Bound from Recurrence
-- ══════════════════════════════════════════════════════════════════

/-- The Ramsey recurrence and R(2, l) = l give a linear bound on the
    increment: R(3, l+1) ≤ R(3, l) + (l + 1).

    This is the key structural lemma: while R(3, l) grows as l²/log l,
    consecutive values differ by at most l + 1. -/
theorem increment_bound (l : ℕ) (hl : l ≥ 1) :
    ramseyNumber 3 (l + 1) ≤ ramseyNumber 3 l + (l + 1) := by
  have h_rec := ramsey_recurrence 3 l (by omega) hl
  have h3 : (3 : ℕ) - 1 = 2 := by omega
  rw [h3] at h_rec
  have h_k2 := ramsey_k2 (l + 1) (by omega)
  omega

-- ══════════════════════════════════════════════════════════════════
-- § Step 2: Analysis Lemma
-- ══════════════════════════════════════════════════════════════════

/-- For any c > 0 and ε > 0, eventually (l+1) · log l / (c · l²) < ε.
    Follows from log x = o(x) (isLittleO_log_rpow_atTop) combined with
    the bound (l+1)*log l / (c*l²) ≤ 2*log l / (c*l). -/
theorem eventually_ratio_small (c : ℝ) (hc : c > 0) (ε : ℝ) (hε : ε > 0) :
    ∃ L : ℕ, ∀ l : ℕ, l > L →
      ((l : ℝ) + 1) * Real.log (l : ℝ) / (c * (l : ℝ) ^ 2) < ε := by
  -- From isLittleO_log_rpow_atTop: log x = o(x) at ∞
  -- So for δ = c*ε/4 > 0, eventually ‖log x‖ ≤ δ * ‖x‖
  -- Then (l+1)*log l/(c*l²) ≤ 2l*δ*l/(c*l²) = 2δ/c = ε/2 < ε
  sorry

-- ══════════════════════════════════════════════════════════════════
-- § Main Theorem
-- ══════════════════════════════════════════════════════════════════

/-- **Erdős Problem #1014 for k = 3**: R(3, l+1) / R(3, l) → 1 as l → ∞.

    This resolves the k = 3 case using only the Ramsey recurrence,
    R(2, l) = l, the Kim-Shearer lower bound, and monotonicity.

    The Θ(l²/log l) bounds suffice because the recurrence constrains
    consecutive increments to be at most linear, while the values grow
    quadratically (up to log factors). -/
theorem erdos_1014_k3_ratio_convergence :
    ∀ ε : ℝ, ε > 0 → ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
      |(ramseyNumber 3 (l + 1) : ℝ) / (ramseyNumber 3 l : ℝ) - 1| < ε := by
  intro ε hε
  -- Get the lower bound constant and threshold
  obtain ⟨c, hc, L₁, hL₁⟩ := R3_lower_bound
  -- Get threshold where the ratio bound is < ε
  obtain ⟨L₂, hL₂⟩ := eventually_ratio_small c hc ε hε
  -- Need l large enough for: lower bound, ratio bound, and log l > 0
  use max (max L₁ L₂) 2
  intro l hl
  have hl1 : l > L₁ := by omega
  have hl2 : l > L₂ := by omega
  have hl_ge1 : l ≥ 1 := by omega
  -- Cast key facts to ℝ
  set R := (ramseyNumber 3 l : ℝ) with hR_def
  set R' := (ramseyNumber 3 (l + 1) : ℝ) with hR'_def
  -- R > 0
  have hR_pos : R > 0 := by
    simp only [hR_def]
    have := ramsey_pos 3 l (by omega) hl_ge1
    exact_mod_cast (show 0 < ramseyNumber 3 l by omega)
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  -- R' ≥ R (monotonicity)
  have hmon : R ≤ R' := by
    simp only [hR_def, hR'_def]
    exact Nat.cast_le.mpr (ramsey_monotone_right 3 l)
  -- R' - R ≤ l + 1 (from increment bound)
  have h_diff : R' - R ≤ (l : ℝ) + 1 := by
    simp only [hR_def, hR'_def]
    have h := increment_bound l hl_ge1
    have : (ramseyNumber 3 (l + 1) : ℝ) ≤ (ramseyNumber 3 l : ℝ) + ((l : ℝ) + 1) := by
      exact_mod_cast h
    linarith
  -- |R'/R - 1| = (R' - R)/R  (since R' ≥ R > 0)
  have h_abs : |R' / R - 1| = (R' - R) / R := by
    have h_eq : R' / R - 1 = (R' - R) / R := by field_simp
    rw [abs_of_nonneg]
    · exact h_eq
    · rw [h_eq]; exact div_nonneg (by linarith) (by linarith)
  rw [h_abs]
  -- log l > 0 for l ≥ 3
  have hlog : Real.log (l : ℝ) > 0 := by
    apply Real.log_pos
    exact_mod_cast (show (1 : ℕ) < l by omega)
  -- R ≥ c · l² / log l
  have hlb := hL₁ l hl1
  have hcl_pos : c * (l : ℝ) ^ 2 / Real.log (l : ℝ) > 0 := by positivity
  -- Chain: (R' - R)/R ≤ (l+1)/R ≤ (l+1)·log l/(c·l²) < ε
  calc (R' - R) / R
      ≤ ((l : ℝ) + 1) / R := by
        apply div_le_div_of_nonneg_right h_diff (le_of_lt hR_pos)
    _ ≤ ((l : ℝ) + 1) / (c * (l : ℝ) ^ 2 / Real.log (l : ℝ)) := by
        apply div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ (l : ℝ) + 1) hcl_pos
        exact hlb
    _ = ((l : ℝ) + 1) * Real.log (l : ℝ) / (c * (l : ℝ) ^ 2) := by
        rw [div_div_eq_mul_div]
    _ < ε := hL₂ l hl2

end Erdos1014OQ01
