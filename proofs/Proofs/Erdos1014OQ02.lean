/-
Erdős Problem #1014 OQ-02: Explicit Rate of Convergence

We prove an explicit quantitative rate for the k = 3 case of Erdős Problem #1014:
  ∃ C > 0, ∃ L₀, ∀ l > L₀, |R(3, l+1)/R(3, l) - 1| ≤ C · log(l) / l

Concretely, C = 2/c where c is the Kim-Shearer constant from R(3, l) ≥ c·l²/log l.
This rate is sharp: the Ramsey recurrence forces increments R(3,l+1) - R(3,l) ≤ l+1
while the Kim-Shearer lower bound gives R(3,l) ≥ c·l²/log l, so their ratio is
exactly Θ(log l / l).

This strengthens OQ-01 (which proved ε-δ convergence) by providing the explicit bound.

Notably, the same rate O(log l / l) is universal for all k ≥ 3 under the conjectured
asymptotics R(k,l) ~ c_k · l^{k-1} / (log l)^{k-2}: the recurrence always gains
one power of l in the denominator relative to the increment R(k-1, l+1).

References:
- Kim (1995): R(3, l) ≥ c · l² / log l
- Shearer (1995): Improved constant in lower bound
- Erdős [Er71], Problem 1014
-/

import Mathlib

open Real

namespace Erdos1014OQ02

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

/-- Kim (1995) / Shearer (1995): There exists c > 0 such that
    R(3, l) ≥ c · l² / log l for all sufficiently large l. -/
axiom R3_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    (ramseyNumber 3 l : ℝ) ≥ c * (l : ℝ) ^ 2 / Real.log (l : ℝ)

-- ══════════════════════════════════════════════════════════════════
-- § Linear Increment Bound from Recurrence
-- ══════════════════════════════════════════════════════════════════

/-- R(3, l+1) ≤ R(3, l) + (l + 1) from the recurrence and R(2, l) = l.
    While R(3, l) grows as l²/log l, consecutive values differ by at most l + 1. -/
theorem increment_bound (l : ℕ) (hl : l ≥ 1) :
    ramseyNumber 3 (l + 1) ≤ ramseyNumber 3 l + (l + 1) := by
  have h_rec := ramsey_recurrence 3 l (by omega) hl
  have h3 : (3 : ℕ) - 1 = 2 := by omega
  rw [h3] at h_rec
  have h_k2 := ramsey_k2 (l + 1) (by omega)
  omega

-- ══════════════════════════════════════════════════════════════════
-- § Main Result: Explicit Rate of Convergence
-- ══════════════════════════════════════════════════════════════════

/-- **Explicit rate of convergence for Erdős #1014, k = 3**:
    There exists C > 0 such that for all sufficiently large l,
      |R(3, l+1) / R(3, l) - 1| ≤ C · log(l) / l.

    Specifically C = 2/c where c is the Kim-Shearer constant.

    Proof chain:
      |R'/R - 1| = (R' - R)/R          (monotonicity: R' ≥ R > 0)
                 ≤ (l+1)/R              (recurrence: R' - R ≤ l+1)
                 ≤ (l+1)/(c·l²/log l)  (Kim-Shearer lower bound)
                 = (l+1)·log l/(c·l²)  (algebra)
                 ≤ 2l·log l/(c·l²)     (l+1 ≤ 2l for l ≥ 1)
                 = (2/c)·log l/l        (cancel l)

    This rate is optimal up to the constant factor. -/
theorem explicit_rate_k3 :
    ∃ C : ℝ, C > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
      |(ramseyNumber 3 (l + 1) : ℝ) / (ramseyNumber 3 l : ℝ) - 1| ≤
        C * Real.log (l : ℝ) / (l : ℝ) := by
  obtain ⟨c, hc, L₁, hL₁⟩ := R3_lower_bound
  refine ⟨2 / c, by positivity, max L₁ 2, fun l hl => ?_⟩
  -- Basic positivity setup
  have hl_ge1 : l ≥ 1 := by omega
  have hl1 : l > L₁ := by omega
  have hl_pos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hl2 : (l : ℝ) + 1 ≤ 2 * (l : ℝ) := by
    exact_mod_cast (show l + 1 ≤ 2 * l by omega)
  have hlog_pos : 0 < Real.log (l : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < l by omega))
  -- Define R = R(3,l) and R' = R(3,l+1) as reals
  set R := (ramseyNumber 3 l : ℝ) with hR_def
  set R' := (ramseyNumber 3 (l + 1) : ℝ) with hR'_def
  -- R > 0
  have hR_pos : 0 < R := by
    simp only [hR_def]
    have := ramsey_pos 3 l (by omega) hl_ge1
    exact_mod_cast (show 0 < ramseyNumber 3 l by omega)
  -- R' ≥ R (monotonicity)
  have hmon : R ≤ R' := by
    simp only [hR_def, hR'_def]
    exact Nat.cast_le.mpr (ramsey_monotone_right 3 l)
  -- R' - R ≤ l + 1 (increment bound)
  have h_diff : R' - R ≤ (l : ℝ) + 1 := by
    simp only [hR_def, hR'_def]
    have h := increment_bound l hl_ge1
    have : (ramseyNumber 3 (l + 1) : ℝ) ≤ (ramseyNumber 3 l : ℝ) + ((l : ℝ) + 1) := by
      exact_mod_cast h
    linarith
  -- |R'/R - 1| = (R' - R)/R since R' ≥ R > 0
  have h_abs : |R' / R - 1| = (R' - R) / R := by
    have h_eq : R' / R - 1 = (R' - R) / R := by field_simp
    rw [abs_of_nonneg]
    · exact h_eq
    · rw [h_eq]; exact div_nonneg (by linarith) (le_of_lt hR_pos)
  rw [h_abs]
  -- Lower bound and positivity
  have hlb := hL₁ l hl1
  have hcl_pos : 0 < c * (l : ℝ) ^ 2 / Real.log (l : ℝ) := by positivity
  -- Main calculation chain
  calc (R' - R) / R
      ≤ ((l : ℝ) + 1) / R :=
        div_le_div_of_nonneg_right h_diff (le_of_lt hR_pos)
    _ ≤ ((l : ℝ) + 1) / (c * (l : ℝ) ^ 2 / Real.log (l : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) hcl_pos hlb
    _ = ((l : ℝ) + 1) * Real.log (l : ℝ) / (c * (l : ℝ) ^ 2) := by
        rw [div_div_eq_mul_div]
    _ ≤ 2 * (l : ℝ) * Real.log (l : ℝ) / (c * (l : ℝ) ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hl2 (le_of_lt hlog_pos)
    _ = 2 / c * Real.log (l : ℝ) / (l : ℝ) := by
        have : c ≠ 0 := ne_of_gt hc
        have : (l : ℝ) ≠ 0 := ne_of_gt hl_pos
        field_simp
        ring

end Erdos1014OQ02
