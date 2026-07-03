/-
Erdős Problem #1014 OQ-04: The k = 4 Case via Mattheus–Verstraëte Bounds

The parent problem (Erdős #1014) asks, for fixed k ≥ 3, whether
  R(k, l+1) / R(k, l) → 1  as  l → ∞.
OQ-01/OQ-02 handle k = 3 via the recurrence R(3,l+1) ≤ R(3,l) + (l+1)
together with the Kim–Shearer lower bound R(3,l) ≥ c·l²/log l.

This file settles the **k = 4 case** using the same "increment vs. size"
principle, but now the increment is controlled by R(3, ·) (which is only
O(l²/log l)) while the size R(4, l) is Ω(l³/(log l)⁴) by the celebrated
Mattheus–Verstraëte theorem (Annals of Mathematics, 2024).

Main results:
  (1) `increment_bound_k4`: the Ramsey recurrence gives
        R(4, l+1) ≤ R(4, l) + R(3, l+1).
  (2) `log_cubed_le_mul`: quantitative form of (log l)³ = o(l).
  (3) `R4_ratio_convergence`: R(4, l+1)/R(4, l) → 1 as l → ∞.
      Proof: |R(4,l+1)/R(4,l) - 1| = (R(4,l+1)-R(4,l))/R(4,l)
                                    ≤ R(3,l+1)/R(4,l)
                                    ≤ (4C/c) · (log l)³ / l → 0,
      since (log l)³ = o(l).
  (4) `R4_rate_of_convergence`: an explicit O((log l)³ / l) rate bound.

The proof is *conditional on* two deep (axiomatized) inputs that are not in
Mathlib:
  - Mattheus–Verstraëte lower bound  R(4, l) ≥ c·l³/(log l)⁴   (`R4_lower_MV`)
  - Ajtai–Komlós–Szemerédi upper bound R(3, l) ≤ C·l²/log l    (`R3_upper`,
    imported from `Proofs.Erdos1014Problem`).
Both are established theorems in the literature; the *combination* proving
the ratio convergence for k = 4 is carried out here in full.

References:
- Erdős [Er71], Problem 1014
- S. Mattheus, J. Verstraëte, "The asymptotics of r(4,t)",
  Annals of Mathematics 199 (2024): R(4,t) = Θ(t³/log⁴ t) up to the log gap.
- Ajtai–Komlós–Szemerédi (1980): R(3,l) ≤ C·l²/log l.
-/

import Mathlib
import Proofs.Erdos1014Problem

open Real Filter Topology

namespace Erdos1014OQ04

-- All axioms (ramseyNumber, ramsey_monotone_right, ramsey_recurrence,
-- R3_upper, …) and theorems (ramsey_pos) are imported from
-- Proofs.Erdos1014Problem.

/-- **Mattheus–Verstraëte (2024)**: R(4, l) = Ω(l³/(log l)⁴).
    There exist c > 0 and L₀ with R(4, l) ≥ c·l³/(log l)⁴ for all l > L₀.

    This is the lower-bound half of the Annals 2024 result
    R(4, t) = Θ̃(t³) (with polylog gap). Not available in Mathlib, so it is
    stated as an axiom (a hypothesis of the k = 4 argument). -/
axiom R4_lower_MV :
  ∃ c : ℝ, c > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    (ramseyNumber 4 l : ℝ) ≥ c * (l : ℝ) ^ 3 / (Real.log l) ^ 4

-- ══════════════════════════════════════════════════════════════════
-- § Step 1: The increment bound for k = 4
-- ══════════════════════════════════════════════════════════════════

/-- The Ramsey recurrence R(k,l+1) ≤ R(k,l) + R(k-1,l+1) at k = 4:
      R(4, l+1) ≤ R(4, l) + R(3, l+1).
    Unlike the k = 3 case (where R(2,l+1) = l+1 is linear), the increment
    here is R(3,l+1) = O(l²/log l) — still asymptotically negligible against
    R(4, l) = Ω(l³/(log l)⁴). -/
theorem increment_bound_k4 (l : ℕ) (hl : l ≥ 1) :
    ramseyNumber 4 (l + 1) ≤ ramseyNumber 4 l + ramseyNumber 3 (l + 1) := by
  have h := ramsey_recurrence 4 l (by omega) hl
  simpa only [show (4 : ℕ) - 1 = 3 from rfl] using h

-- ══════════════════════════════════════════════════════════════════
-- § Step 2: (log l)³ = o(l)
-- ══════════════════════════════════════════════════════════════════

/-- For any target slope `m > 0`, eventually `(log l)³ ≤ m · l`.

    This is the quantitative form of `(log l)³ = o(l)`. We use
    `log x = o(x^(1/3))`: choosing the little-o constant to be `m^(1/3)`
    gives `log l ≤ m^(1/3) · l^(1/3)`, and cubing yields
    `(log l)³ ≤ m · (l^(1/3))³ = m · l`. -/
theorem log_cubed_le_mul (m : ℝ) (hm : m > 0) :
    ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
      (Real.log (l : ℝ)) ^ 3 ≤ m * (l : ℝ) := by
  set K : ℝ := m ^ ((1 : ℝ) / 3) with hK_def
  have hK : K > 0 := by rw [hK_def]; exact Real.rpow_pos_of_pos hm _
  -- log =o(x^(1/3))
  have ho := Real.isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 3 by norm_num)
  have hev := ho.bound hK
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (⌈N⌉₊ + 1) 2, fun l hl => ?_⟩
  have hl_pos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hlog_pos : 0 < Real.log (l : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < l by omega))
  have hl_ge_N : N ≤ (l : ℝ) :=
    le_trans (Nat.le_ceil N) (by exact_mod_cast (show ⌈N⌉₊ ≤ l by omega))
  have hb := hN (l : ℝ) hl_ge_N
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog_pos,
      abs_of_pos (Real.rpow_pos_of_pos hl_pos _)] at hb
  -- hb : log l ≤ K * l^(1/3)
  have hb0 : (0 : ℝ) ≤ Real.log (l : ℝ) := hlog_pos.le
  have hRHS0 : (0 : ℝ) ≤ K * (l : ℝ) ^ ((1 : ℝ) / 3) := le_trans hb0 hb
  -- cube both sides (nonnegative), manually to avoid version-sensitive lemmas
  have hcube : (Real.log (l : ℝ)) ^ 3 ≤ (K * (l : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
    calc (Real.log (l : ℝ)) ^ 3
        = Real.log (l : ℝ) * Real.log (l : ℝ) * Real.log (l : ℝ) := by ring
      _ ≤ (K * (l : ℝ) ^ ((1 : ℝ) / 3)) * (K * (l : ℝ) ^ ((1 : ℝ) / 3)) *
            (K * (l : ℝ) ^ ((1 : ℝ) / 3)) := by
          apply mul_le_mul (mul_le_mul hb hb hb0 hRHS0) hb hb0 (mul_nonneg hRHS0 hRHS0)
      _ = (K * (l : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by ring
  -- (l^(1/3))³ = l
  have hpow : ((l : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (l : ℝ) := by
    rw [← Real.rpow_natCast ((l : ℝ) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hl_pos.le,
        show (1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 1 by push_cast; norm_num, Real.rpow_one]
  -- K³ = m
  have hKcube : K ^ (3 : ℕ) = m := by
    rw [hK_def, ← Real.rpow_natCast (m ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hm.le,
        show (1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 1 by push_cast; norm_num, Real.rpow_one]
  calc (Real.log (l : ℝ)) ^ 3
      ≤ (K * (l : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := hcube
    _ = K ^ 3 * ((l : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by rw [mul_pow]
    _ = m * (l : ℝ) := by rw [hKcube, hpow]

-- ══════════════════════════════════════════════════════════════════
-- § Step 3: R(4, l+1)/R(4, l) → 1  (the k = 4 case of Erdős #1014)
-- ══════════════════════════════════════════════════════════════════

/-- **Erdős Problem #1014 for k = 4** (conditional on Mattheus–Verstraëte
    and AKS bounds): R(4, l+1)/R(4, l) → 1 as l → ∞.

    Proof sketch:
    - R(4,l+1) - R(4,l) ≤ R(3,l+1) ≤ C·(l+1)²/log(l+1) ≤ 4C·l²/log l  (increment)
    - R(4,l) ≥ c·l³/(log l)⁴                                          (M–V)
    - hence |R(4,l+1)/R(4,l) - 1| = (R(4,l+1)-R(4,l))/R(4,l)
                                  ≤ (4C/c)·(log l)³/l → 0. -/
theorem R4_ratio_convergence :
    ∀ ε : ℝ, ε > 0 → ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
      |(ramseyNumber 4 (l + 1) : ℝ) / (ramseyNumber 4 l : ℝ) - 1| < ε := by
  intro ε hε
  obtain ⟨c, hc, L₁, hL₁⟩ := R4_lower_MV
  obtain ⟨C, hC, L₂, hL₂⟩ := R3_upper
  -- Choose the little-o slope m so that (4C/c)·m ≤ ε/2.
  obtain ⟨L₃, hL₃⟩ := log_cubed_le_mul (c * ε / (8 * C)) (by positivity)
  refine ⟨max (max (max L₁ L₂) L₃) 2, fun l hl => ?_⟩
  have hl1 : l > L₁ := by omega
  have hl2' : l + 1 > L₂ := by omega
  have hl3 : l > L₃ := by omega
  have hl_ge1 : l ≥ 1 := by omega
  have hl_pos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hl1r : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl_ge1
  have hlog : 0 < Real.log (l : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < l by omega))
  have hlog1 : 0 < Real.log ((l : ℝ) + 1) := Real.log_pos (by linarith)
  set R := (ramseyNumber 4 l : ℝ) with hR_def
  set R' := (ramseyNumber 4 (l + 1) : ℝ) with hR'_def
  have hR_pos : R > 0 := by
    simp only [hR_def]
    have := ramsey_pos 4 l (by omega) hl_ge1
    exact_mod_cast (show 0 < ramseyNumber 4 l by omega)
  have hmon : R ≤ R' := by
    simp only [hR_def, hR'_def]
    exact Nat.cast_le.mpr (ramsey_monotone_right 4 l)
  have h_diff : R' - R ≤ (ramseyNumber 3 (l + 1) : ℝ) := by
    simp only [hR_def, hR'_def]
    have h := increment_bound_k4 l hl_ge1
    have : (ramseyNumber 4 (l + 1) : ℝ) ≤
        (ramseyNumber 4 l : ℝ) + (ramseyNumber 3 (l + 1) : ℝ) := by exact_mod_cast h
    linarith
  -- R(3, l+1) ≤ C·(l+1)²/log(l+1) ≤ 4C·l²/log l
  have hR3ub : (ramseyNumber 3 (l + 1) : ℝ) ≤ 4 * C * (l : ℝ) ^ 2 / Real.log (l : ℝ) := by
    have hub := hL₂ (l + 1) hl2'
    push_cast at hub
    have hsq : ((l : ℝ) + 1) ^ 2 ≤ 4 * (l : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (l:ℝ) - 1) (by linarith : (0:ℝ) ≤ 3*(l:ℝ) + 1)]
    have hlogle : Real.log (l : ℝ) ≤ Real.log ((l : ℝ) + 1) :=
      Real.log_le_log hl_pos (by linarith)
    have hstep : C * ((l : ℝ) + 1) ^ 2 / Real.log ((l : ℝ) + 1) ≤
        4 * C * (l : ℝ) ^ 2 / Real.log (l : ℝ) := by
      calc C * ((l : ℝ) + 1) ^ 2 / Real.log ((l : ℝ) + 1)
          ≤ 4 * C * (l : ℝ) ^ 2 / Real.log ((l : ℝ) + 1) := by
            apply div_le_div_of_nonneg_right _ hlog1.le
            nlinarith [mul_le_mul_of_nonneg_left hsq (le_of_lt hC)]
        _ ≤ 4 * C * (l : ℝ) ^ 2 / Real.log (l : ℝ) := by
            apply div_le_div_of_nonneg_left _ hlog hlogle
            positivity
    linarith [hub, hstep]
  have h_abs : |R' / R - 1| = (R' - R) / R := by
    have h_eq : R' / R - 1 = (R' - R) / R := by field_simp
    rw [h_eq, abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hR_pos))]
  rw [h_abs]
  have hlb := hL₁ l hl1
  have hden_pos : (0 : ℝ) < c * (l : ℝ) ^ 3 / (Real.log (l : ℝ)) ^ 4 := by positivity
  have hlog3 := hL₃ l hl3
  have hCne : C ≠ 0 := ne_of_gt hC
  have hcne : c ≠ 0 := ne_of_gt hc
  have hlne : (l : ℝ) ≠ 0 := ne_of_gt hl_pos
  have hlogne : Real.log (l : ℝ) ≠ 0 := ne_of_gt hlog
  -- Algebraic simplification of the compound fraction
  have hkey : (4 * C * (l : ℝ) ^ 2 / Real.log (l : ℝ)) /
        (c * (l : ℝ) ^ 3 / (Real.log (l : ℝ)) ^ 4)
      = 4 * C / c * ((Real.log (l : ℝ)) ^ 3 / (l : ℝ)) := by
    field_simp
    ring
  calc (R' - R) / R
      ≤ (ramseyNumber 3 (l + 1) : ℝ) / R :=
        div_le_div_of_nonneg_right h_diff (le_of_lt hR_pos)
    _ ≤ (4 * C * (l : ℝ) ^ 2 / Real.log (l : ℝ)) / R :=
        div_le_div_of_nonneg_right hR3ub (le_of_lt hR_pos)
    _ ≤ (4 * C * (l : ℝ) ^ 2 / Real.log (l : ℝ)) /
          (c * (l : ℝ) ^ 3 / (Real.log (l : ℝ)) ^ 4) := by
        apply div_le_div_of_nonneg_left _ hden_pos hlb
        positivity
    _ = 4 * C / c * ((Real.log (l : ℝ)) ^ 3 / (l : ℝ)) := hkey
    _ ≤ 4 * C / c * ((c * ε / (8 * C) * (l : ℝ)) / (l : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (div_pos (mul_pos (by norm_num) hC) hc).le
        exact div_le_div_of_nonneg_right hlog3 hl_pos
    _ = ε / 2 := by field_simp; ring
    _ < ε := by linarith

-- ══════════════════════════════════════════════════════════════════
-- § Step 4: Explicit rate bound O((log l)³ / l)
-- ══════════════════════════════════════════════════════════════════

/-- **Explicit convergence rate for k = 4**: there exist `A > 0` and `L₀`
    with, for all `l > L₀`,
      |R(4,l+1)/R(4,l) - 1| ≤ A · (log l)³ / l.
    Here `A = 4C/c`, with `c` the Mattheus–Verstraëte lower constant and `C`
    the AKS upper constant for R(3, ·). Since (log l)³ = o(l), the bound → 0. -/
theorem R4_rate_of_convergence :
    ∃ A : ℝ, A > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
      |(ramseyNumber 4 (l + 1) : ℝ) / (ramseyNumber 4 l : ℝ) - 1| ≤
        A * (Real.log (l : ℝ)) ^ 3 / (l : ℝ) := by
  obtain ⟨c, hc, L₁, hL₁⟩ := R4_lower_MV
  obtain ⟨C, hC, L₂, hL₂⟩ := R3_upper
  refine ⟨4 * C / c, by positivity, max (max L₁ L₂) 2, fun l hl => ?_⟩
  have hl1 : l > L₁ := by omega
  have hl2' : l + 1 > L₂ := by omega
  have hl_ge1 : l ≥ 1 := by omega
  have hl_pos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
  have hl1r : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl_ge1
  have hlog : 0 < Real.log (l : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < l by omega))
  have hlog1 : 0 < Real.log ((l : ℝ) + 1) := Real.log_pos (by linarith)
  set R := (ramseyNumber 4 l : ℝ) with hR_def
  set R' := (ramseyNumber 4 (l + 1) : ℝ) with hR'_def
  have hR_pos : R > 0 := by
    simp only [hR_def]
    have := ramsey_pos 4 l (by omega) hl_ge1
    exact_mod_cast (show 0 < ramseyNumber 4 l by omega)
  have hmon : R ≤ R' := by
    simp only [hR_def, hR'_def]
    exact Nat.cast_le.mpr (ramsey_monotone_right 4 l)
  have h_diff : R' - R ≤ (ramseyNumber 3 (l + 1) : ℝ) := by
    simp only [hR_def, hR'_def]
    have h := increment_bound_k4 l hl_ge1
    have : (ramseyNumber 4 (l + 1) : ℝ) ≤
        (ramseyNumber 4 l : ℝ) + (ramseyNumber 3 (l + 1) : ℝ) := by exact_mod_cast h
    linarith
  have hR3ub : (ramseyNumber 3 (l + 1) : ℝ) ≤ 4 * C * (l : ℝ) ^ 2 / Real.log (l : ℝ) := by
    have hub := hL₂ (l + 1) hl2'
    push_cast at hub
    have hsq : ((l : ℝ) + 1) ^ 2 ≤ 4 * (l : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (l:ℝ) - 1) (by linarith : (0:ℝ) ≤ 3*(l:ℝ) + 1)]
    have hlogle : Real.log (l : ℝ) ≤ Real.log ((l : ℝ) + 1) :=
      Real.log_le_log hl_pos (by linarith)
    have hstep : C * ((l : ℝ) + 1) ^ 2 / Real.log ((l : ℝ) + 1) ≤
        4 * C * (l : ℝ) ^ 2 / Real.log (l : ℝ) := by
      calc C * ((l : ℝ) + 1) ^ 2 / Real.log ((l : ℝ) + 1)
          ≤ 4 * C * (l : ℝ) ^ 2 / Real.log ((l : ℝ) + 1) := by
            apply div_le_div_of_nonneg_right _ hlog1.le
            nlinarith [mul_le_mul_of_nonneg_left hsq (le_of_lt hC)]
        _ ≤ 4 * C * (l : ℝ) ^ 2 / Real.log (l : ℝ) := by
            apply div_le_div_of_nonneg_left _ hlog hlogle
            positivity
    linarith [hub, hstep]
  have h_abs : |R' / R - 1| = (R' - R) / R := by
    have h_eq : R' / R - 1 = (R' - R) / R := by field_simp
    rw [h_eq, abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hR_pos))]
  rw [h_abs]
  have hlb := hL₁ l hl1
  have hden_pos : (0 : ℝ) < c * (l : ℝ) ^ 3 / (Real.log (l : ℝ)) ^ 4 := by positivity
  have hCne : C ≠ 0 := ne_of_gt hC
  have hcne : c ≠ 0 := ne_of_gt hc
  have hlne : (l : ℝ) ≠ 0 := ne_of_gt hl_pos
  have hlogne : Real.log (l : ℝ) ≠ 0 := ne_of_gt hlog
  have hkey : (4 * C * (l : ℝ) ^ 2 / Real.log (l : ℝ)) /
        (c * (l : ℝ) ^ 3 / (Real.log (l : ℝ)) ^ 4)
      = 4 * C / c * (Real.log (l : ℝ)) ^ 3 / (l : ℝ) := by
    field_simp
    ring
  calc (R' - R) / R
      ≤ (ramseyNumber 3 (l + 1) : ℝ) / R :=
        div_le_div_of_nonneg_right h_diff (le_of_lt hR_pos)
    _ ≤ (4 * C * (l : ℝ) ^ 2 / Real.log (l : ℝ)) / R :=
        div_le_div_of_nonneg_right hR3ub (le_of_lt hR_pos)
    _ ≤ (4 * C * (l : ℝ) ^ 2 / Real.log (l : ℝ)) /
          (c * (l : ℝ) ^ 3 / (Real.log (l : ℝ)) ^ 4) := by
        apply div_le_div_of_nonneg_left _ hden_pos hlb
        positivity
    _ = 4 * C / c * (Real.log (l : ℝ)) ^ 3 / (l : ℝ) := hkey

end Erdos1014OQ04
