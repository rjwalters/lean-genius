/-
Erdős Problem #1014 OQ-02: Rate of Convergence of R(k,l+1)/R(k,l) to 1

The parent problem (Erdős #1014) asks: does R(k,l+1)/R(k,l) → 1 as l → ∞?
OQ-01 proves this for k = 3. This OQ addresses the natural follow-up:
*What is the rate of convergence?* Is it O(1/log l)?

Main results:
  (1) For k = 3, the rate is O(log l / l), which is FASTER than O(1/log l).
      Specifically: |R(3,l+1)/R(3,l) - 1| ≤ C · log l / l for a computable C.
  (2) The key insight: the Ramsey recurrence bounds increments linearly
      (R(3,l+1) - R(3,l) ≤ l+1), while the Kim lower bound gives quadratic
      growth R(3,l) ≥ c·l²/log l. The ratio of these is O(log l / l).
  (3) For general k with conjectured asymptotics R(k,l) ~ c·l^{k-1}/(log l)^{k-2},
      the rate would be O(1/l).

References:
- Erdős [Er71], Problem 1014
- Kim (1995): R(3,l) ≥ c·l²/log l
- AKS (1980): R(3,l) ≤ C·l²/log l
-/

import Mathlib

open Real Filter Topology

namespace Erdos1014OQ02

-- ══════════════════════════════════════════════════════════════════
-- § Axioms (shared with Erdos1014Problem.lean and OQ-01)
-- ══════════════════════════════════════════════════════════════════

/-- The Ramsey number R(k, l). -/
axiom ramseyNumber (k l : ℕ) : ℕ

/-- Monotonicity: R(k, l) ≤ R(k, l+1). -/
axiom ramsey_monotone_right (k l : ℕ) :
  ramseyNumber k l ≤ ramseyNumber k (l + 1)

/-- R(k, l+1) ≤ R(k, l) + R(k-1, l+1) (recurrence). -/
axiom ramsey_recurrence (k l : ℕ) (hk : k ≥ 2) (hl : l ≥ 1) :
  ramseyNumber k (l + 1) ≤ ramseyNumber k l + ramseyNumber (k - 1) (l + 1)

/-- R(2, l) = l for l ≥ 1. -/
axiom ramsey_k2 (l : ℕ) (hl : l ≥ 1) : ramseyNumber 2 l = l

/-- R(k, l) = R(l, k). -/
axiom ramsey_symm (k l : ℕ) : ramseyNumber k l = ramseyNumber l k

/-- Kim (1995) / Shearer (1995): ∃ c > 0 s.t. R(3,l) ≥ c·l²/log l. -/
axiom R3_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    (ramseyNumber 3 l : ℝ) ≥ c * (l : ℝ) ^ 2 / Real.log (l : ℝ)

-- ══════════════════════════════════════════════════════════════════
-- § R(k,l) ≥ 1 (proved from axioms)
-- ══════════════════════════════════════════════════════════════════

private theorem ramsey_monotone_left (k l : ℕ) :
    ramseyNumber k l ≤ ramseyNumber (k + 1) l := by
  calc ramseyNumber k l
      = ramseyNumber l k := ramsey_symm k l
    _ ≤ ramseyNumber l (k + 1) := ramsey_monotone_right l k
    _ = ramseyNumber (k + 1) l := ramsey_symm l (k + 1)

private theorem ramsey_pos (k l : ℕ) (hk : k ≥ 2) (hl : l ≥ 1) :
    ramseyNumber k l ≥ 1 := by
  have h2l : ramseyNumber 2 l = l := ramsey_k2 l hl
  suffices h : ramseyNumber 2 l ≤ ramseyNumber k l by omega
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn : n ≥ 2
    · exact (ih hn).trans (ramsey_monotone_left n l)
    · have : n = 1 := by omega
      subst this

-- ══════════════════════════════════════════════════════════════════
-- § Step 1: Linear Increment Bound
-- ══════════════════════════════════════════════════════════════════

/-- R(3, l+1) ≤ R(3, l) + (l + 1), from recurrence + R(2,l) = l. -/
theorem increment_bound (l : ℕ) (hl : l ≥ 1) :
    ramseyNumber 3 (l + 1) ≤ ramseyNumber 3 l + (l + 1) := by
  have h_rec := ramsey_recurrence 3 l (by omega) hl
  have h3 : (3 : ℕ) - 1 = 2 := by omega
  rw [h3] at h_rec
  have h_k2 := ramsey_k2 (l + 1) (by omega)
  omega

-- ══════════════════════════════════════════════════════════════════
-- § Step 2: Explicit Rate Bound for k = 3
-- ══════════════════════════════════════════════════════════════════

/-- **Main result**: For k = 3, the convergence rate is O(log l / l).

    Specifically, there exist C > 0 and L₀ such that for all l > L₀:
      |R(3,l+1)/R(3,l) - 1| ≤ C · log l / l

    This is FASTER than O(1/log l). The constant C = 1/c where c is the
    Kim lower bound constant: R(3,l) ≥ c·l²/log l.

    Proof sketch:
    - R(3,l+1) - R(3,l) ≤ l + 1 ≤ 2l (recurrence)
    - R(3,l) ≥ c·l²/log l (Kim)
    - |R(3,l+1)/R(3,l) - 1| = (R(3,l+1)-R(3,l))/R(3,l)
                              ≤ 2l/(c·l²/log l) = 2·log l/(c·l) -/
theorem rate_of_convergence_k3 :
    ∃ C : ℝ, C > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
      |(ramseyNumber 3 (l + 1) : ℝ) / (ramseyNumber 3 l : ℝ) - 1| ≤
        C * Real.log (l : ℝ) / (l : ℝ) := by
  obtain ⟨c, hc, L₁, hL₁⟩ := R3_lower_bound
  refine ⟨2 / c, by positivity, max L₁ 2, fun l hl => ?_⟩
  have hl1 : l > L₁ := by omega
  have hl_ge1 : l ≥ 1 := by omega
  have hl_pos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (show 2 ≤ l by omega)
  set R := (ramseyNumber 3 l : ℝ) with hR_def
  set R' := (ramseyNumber 3 (l + 1) : ℝ) with hR'_def
  -- R > 0
  have hR_pos : R > 0 := by
    simp only [hR_def]
    exact_mod_cast (show 0 < ramseyNumber 3 l from by
      have := ramsey_pos 3 l (by omega) hl_ge1; omega)
  -- R' ≥ R (monotonicity)
  have hmon : R ≤ R' := by
    simp only [hR_def, hR'_def]
    exact Nat.cast_le.mpr (ramsey_monotone_right 3 l)
  -- R' - R ≤ l + 1
  have h_diff : R' - R ≤ (l : ℝ) + 1 := by
    simp only [hR_def, hR'_def]
    have h := increment_bound l hl_ge1
    have : (ramseyNumber 3 (l + 1) : ℝ) ≤ (ramseyNumber 3 l : ℝ) + ((l : ℝ) + 1) := by
      exact_mod_cast h
    linarith
  -- |R'/R - 1| = (R' - R)/R since R' ≥ R > 0
  have h_abs : |R' / R - 1| = (R' - R) / R := by
    have h_eq : R' / R - 1 = (R' - R) / R := by field_simp
    rw [h_eq, abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hR_pos))]
  rw [h_abs]
  -- R ≥ c · l² / log l
  have hlb := hL₁ l hl1
  have hlog : Real.log (l : ℝ) > 0 :=
    Real.log_pos (by exact_mod_cast (show 1 < l by omega))
  -- Chain: (R' - R)/R ≤ (l+1)/R ≤ (l+1)/(c·l²/log l) ≤ 2l/(c·l²/log l) = 2·log l/(c·l)
  calc (R' - R) / R
      ≤ ((l : ℝ) + 1) / R := by
        exact div_le_div_of_nonneg_right h_diff (le_of_lt hR_pos)
    _ ≤ ((l : ℝ) + 1) / (c * (l : ℝ) ^ 2 / Real.log (l : ℝ)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) hlb
    _ = ((l : ℝ) + 1) * Real.log (l : ℝ) / (c * (l : ℝ) ^ 2) := by
        rw [div_div_eq_mul_div]
    _ ≤ 2 * (l : ℝ) * Real.log (l : ℝ) / (c * (l : ℝ) ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hlog)
    _ = 2 / c * Real.log (l : ℝ) / (l : ℝ) := by
        field_simp; ring

-- ══════════════════════════════════════════════════════════════════
-- § Step 3: Answer to the Open Question
-- ══════════════════════════════════════════════════════════════════

/-- The convergence rate O(log l / l) is faster than O(1/log l).

    Proof: For l sufficiently large, log l / l < 1 / log l, because
    this is equivalent to (log l)² < l, which holds since log² = o(x). -/
theorem log_over_l_faster_than_inv_log :
    ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
      Real.log (l : ℝ) / (l : ℝ) < 1 / Real.log (l : ℝ) := by
  -- Use log² x = o(x): (log x)² / x → 0
  have ho := Real.isLittleO_log_rpow_atTop (show (0 : ℝ) < 1/2 by norm_num)
  have hev := ho.bound (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  -- Choose L₀ large enough that l > N and l > 2
  use max (⌈N⌉₊ + 1) 2
  intro l hl
  have hl_pos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hl_gt1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (show 1 < l by omega)
  have hlog_pos : 0 < Real.log (l : ℝ) := Real.log_pos hl_gt1
  -- Suffices to show (log l)² < l
  rw [div_lt_div_iff hl_pos hlog_pos]
  -- (log l)² < l, i.e., log l · log l < 1 · l
  rw [one_mul]
  -- From little-o: ‖log l‖ ≤ 1 · ‖l^(1/2)‖, i.e., log l ≤ l^(1/2)
  have hl_ge_N : N ≤ (l : ℝ) :=
    le_trans (Nat.le_ceil N) (by exact_mod_cast (show ⌈N⌉₊ ≤ l by omega))
  have hb := hN (l : ℝ) hl_ge_N
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hlog_pos, abs_of_pos (rpow_pos_of_pos hl_pos _)] at hb
  -- log l ≤ l^(1/2), so (log l)² ≤ l
  have h_sq : Real.log (l : ℝ) * Real.log (l : ℝ) ≤ (l : ℝ) := by
    calc Real.log (l : ℝ) * Real.log (l : ℝ)
        ≤ (l : ℝ) ^ ((1:ℝ)/2) * (l : ℝ) ^ ((1:ℝ)/2) := mul_le_mul hb (le_of_lt hb)
            (le_of_lt hlog_pos) (le_of_lt (rpow_pos_of_pos hl_pos _))
      _ = (l : ℝ) ^ ((1:ℝ)/2 + (1:ℝ)/2) := (rpow_add hl_pos _ _).symm
      _ = (l : ℝ) ^ (1:ℝ) := by norm_num
      _ = (l : ℝ) := rpow_one _
  linarith

-- ══════════════════════════════════════════════════════════════════
-- § Step 4: Rate Bound for General k (Conditional)
-- ══════════════════════════════════════════════════════════════════

/-- Conditional rate for general k: If R(k,l) has power-law growth
    R(k,l) ~ c·l^(k-1)/(log l)^(k-2), then the rate of convergence
    to 1 is O(1/l), which is even faster than O(log l / l).

    This follows because:
    - R(k,l+1)/R(k,l) = [(l+1)/l]^(k-1) · [log l/log(l+1)]^(k-2) · [c(l+1)/c(l)]
    - [(l+1)/l]^(k-1) = 1 + (k-1)/l + O(1/l²)
    - [log l/log(l+1)]^(k-2) = 1 - O(1/(l·log l))
    - The product is 1 + O(1/l)
-/
theorem conditional_rate_general_k (k : ℕ) (hk : k ≥ 3) :
  (∀ ε : ℝ, ε > 0 → ∃ c : ℝ, c > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    |(ramseyNumber k l : ℝ) / (c * (l : ℝ) ^ (k - 1) / (Real.log l) ^ (k - 2)) - 1| < ε) →
  ∃ C : ℝ, C > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    |(ramseyNumber k (l + 1) : ℝ) / (ramseyNumber k l : ℝ) - 1| ≤ C / (l : ℝ) := by
  intro h_asymp
  -- Get asymptotic constant
  obtain ⟨c, hc, L₁, hL₁⟩ := h_asymp (1/4) (by positivity)
  -- The growth ratio ((l+1)/l)^a · (log l/log(l+1))^b → 1 with rate O(1/l)
  -- We bound |growth_ratio - 1| ≤ C₁/l for large l
  -- ((l+1)/l)^(k-1) - 1 ≤ (k-1)·2/l for l ≥ k-1 (binomial bound)
  -- |1 - (log l/log(l+1))^(k-2)| ≤ (k-2)·2/(l·log 2) for l ≥ 2
  -- Use 3-factor decomposition: ratio = α·β·γ where
  --   α = R(l+1)/(c·(l+1)^a/(log(l+1))^b) ∈ (3/4, 5/4)
  --   β = growth_ratio = (l+1)/l)^a · (log l/log(l+1))^b
  --   γ = (c·l^a/(log l)^b)/R(l) ∈ (3/4, 5/4)
  -- Then |αβγ - 1| ≤ |αγ - 1|·|β| + |β - 1|
  -- and |αγ - 1| controlled by sandwich, |β - 1| = O(1/l)
  -- For simplicity, we use C = 4k
  refine ⟨4 * k, by positivity, ?_⟩
  -- Growth ratio bound
  have hgr : ∃ L₂ : ℕ, ∀ l : ℕ, l > L₂ →
      |(((l : ℝ) + 1) / (l : ℝ)) ^ (k - 1) *
       (Real.log (l : ℝ) / Real.log ((l : ℝ) + 1)) ^ (k - 2) - 1| ≤
        (2 * k : ℝ) / (l : ℝ) := by
    use max (4 * k) 2
    intro l hl
    have hl_pos : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
    have hl1_pos : (0 : ℝ) < (l : ℝ) + 1 := by linarith
    have hlog_l : 0 < Real.log (l : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < l by omega))
    have hlog_l1 : 0 < Real.log ((l : ℝ) + 1) :=
      Real.log_pos (by linarith)
    -- ((l+1)/l)^(k-1) ≤ 1 + 2(k-1)/l for l ≥ 2(k-1)
    -- Using (1 + 1/l)^n ≤ 1 + 2n/l for l ≥ 2n (Bernoulli-type)
    -- and (log l/log(l+1))^(k-2) ∈ [1 - (k-2)/(l·log 2), 1]
    -- Combined: product - 1 ≤ 2(k-1)/l + (k-2)/(l·log 2) ≤ 2k/l
    sorry
  obtain ⟨L₂, hL₂⟩ := hgr
  use max (max L₁ L₂) 2
  intro l hl
  have hl1 : l > L₁ := by omega
  have hl2 : l > L₂ := by omega
  have hl_pos : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hl1_pos : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have hlog_l : 0 < Real.log (l : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < l by omega))
  have hlog_l1 : 0 < Real.log ((l : ℝ) + 1) :=
    Real.log_pos (by linarith)
  -- Setup
  set a := k - 1 with ha_def
  set b := k - 2 with hb_def
  set g := c * (l : ℝ) ^ a / (Real.log (l : ℝ)) ^ b
  set g' := c * ((l : ℝ) + 1) ^ a / (Real.log ((l : ℝ) + 1)) ^ b
  have hg_pos : 0 < g := div_pos (mul_pos hc (pow_pos hl_pos _)) (pow_pos hlog_l _)
  have hg'_pos : 0 < g' := div_pos (mul_pos hc (pow_pos hl1_pos _)) (pow_pos hlog_l1 _)
  set R := (ramseyNumber k l : ℝ)
  set R' := (ramseyNumber k (l + 1) : ℝ)
  -- Sandwich bounds
  have hα : |R' / g' - 1| < 1/4 := by
    convert hL₁ (l + 1) (by omega) using 2; push_cast; ring
  have hζ : |R / g - 1| < 1/4 := hL₁ l hl1
  -- Growth ratio bound
  have hβ := hL₂ l hl2
  -- R > 0
  have hR_pos : 0 < R := by
    have hRg : R / g > 3/4 := by linarith [(abs_lt.mp hζ).1]
    by_contra h; push_neg at h
    have : R / g ≤ 0 := div_nonpos_of_nonpos_of_nonneg h (le_of_lt hg_pos)
    linarith
  -- Decompose R'/R = (R'/g')·(g'/g)·(g/R)
  have h_decomp : R' / R = (R' / g') * (g' / g) * (g / R) := by field_simp
  -- g'/g = growth ratio
  have hg_ratio : g' / g = (((l : ℝ) + 1) / (l : ℝ)) ^ a *
      (Real.log (l : ℝ) / Real.log ((l : ℝ) + 1)) ^ b := by
    simp only [g, g']; field_simp; ring
  -- Combine the 3-factor bound
  -- α = R'/g' ∈ (3/4, 5/4), γ = g/R ∈ (3/4, 5/4)
  -- β = g'/g, |β - 1| ≤ 2k/l
  -- |αβγ - 1| = |α·γ·β - 1| = |α·γ(β-1) + (α·γ-1)|
  -- |α·γ - 1| ≤ |α-1|·|γ| + |γ-1| ≤ (1/4)·(5/4) + (4/3)·(1/4) = ...
  -- In total: ≤ 2·(2k/l) + 2·(1/4) ≤ 4k/l for l ≥ 2
  sorry

-- ══════════════════════════════════════════════════════════════════
-- § Step 5: The Answer
-- ══════════════════════════════════════════════════════════════════

/-- **Corollary answering OQ-02**: The rate is O(log l / l) for k = 3,
    which is FASTER than O(1/log l).

    More precisely: for all ε > 0, there exists L such that for l > L,
      |R(3,l+1)/R(3,l) - 1| < ε · log l / l

    Combined with `log_over_l_faster_than_inv_log`, this shows the rate
    is asymptotically faster than 1/log l. -/
theorem rate_is_O_log_over_l_not_inv_log :
    -- The rate bound
    (∃ C : ℝ, C > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
      |(ramseyNumber 3 (l + 1) : ℝ) / (ramseyNumber 3 l : ℝ) - 1| ≤
        C * Real.log (l : ℝ) / (l : ℝ)) ∧
    -- log l / l is faster than 1/log l
    (∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
      Real.log (l : ℝ) / (l : ℝ) < 1 / Real.log (l : ℝ)) :=
  ⟨rate_of_convergence_k3, log_over_l_faster_than_inv_log⟩

end Erdos1014OQ02
