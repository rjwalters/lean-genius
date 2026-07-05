/-
Erdős Problem #1014 OQ-04: Ratio Convergence for k = 4 via Mattheus–Verstraëte Bounds

We prove that R(4, l+1) / R(4, l) → 1 as l → ∞, resolving the k = 4 case
of Erdős Problem #1014.

The parent problem asks: for fixed k ≥ 3, does R(k, l+1)/R(k, l) → 1 as l → ∞?
OQ-01 resolved k = 3 using the Kim–Shearer quadratic lower bound R(3,l) ≥ c·l²/log l.
This file resolves **k = 4** using the recent breakthrough of Mattheus and
Verstraëte (2024), who determined the order of magnitude of the off-diagonal
Ramsey number R(4,l):
      R(4, l) = Θ( l³ / (log l)⁴ ).

The proof structure exactly mirrors OQ-01 one dimension up:

  (1) The Ramsey recurrence R(4, l+1) ≤ R(4, l) + R(3, l+1)   [proved in OQ-01]
  (2) The classical AKS upper bound R(3, l) ≤ C · l²/log l    [axiom]
  (3) The Mattheus–Verstraëte lower bound R(4, l) ≥ c · l³/(log l)⁴  [axiom]

Key insight: the increment R(4,l+1) − R(4,l) ≤ R(3,l+1) grows only like l²
(one Ramsey dimension below), while R(4,l) itself grows like l³.  Hence
      R(4,l+1)/R(4,l) − 1  ≤  R(3,l+1)/R(4,l)
                           ≤  (4C/c) · (log l)⁴ / l  →  0.

So the *cubic* growth of R(4,l) dominates the *quadratic* increment, forcing the
ratio to 1.  The polylog factors are irrelevant to convergence: any bounds of
order l² (numerator) and l³ (denominator) suffice, which is exactly the
qualitative content the Mattheus–Verstraëte theorem now guarantees for k = 4.

Axioms used (both are published theorems, stated as hypotheses):
  * R3_upper_bound_aks — Ajtai–Komlós–Szemerédi (1980): R(3,l) = O(l²/log l).
  * R4_lower_bound_mv  — Mattheus–Verstraëte (2024): R(4,l) = Ω(l³/(log l)⁴).
All Ramsey-number infrastructure (the *definition* and the recurrence,
monotonicity, positivity) is imported from OQ-01 and is axiom-free.

References:
- Erdős [Er71], Problem 1014, p. 99
- Ajtai, Komlós, Szemerédi (1980): R(3,l) ≤ C·l²/log l
- Mattheus, Verstraëte, "The asymptotics of r(4,t)", Annals of Mathematics (2024):
  R(4,l) = Θ(l³/(log l)⁴)
- <https://erdosproblems.com/1014>
-/

import Mathlib
import Proofs.Erdos1014OQ01

open Real Filter Topology Asymptotics

namespace Erdos1014OQ04

-- ══════════════════════════════════════════════════════════════════
-- § Deep-result axioms (published theorems, stated as hypotheses)
-- ══════════════════════════════════════════════════════════════════

/-- **Ajtai–Komlós–Szemerédi (1980)** upper bound: there is a constant `C > 0`
    with `R(3, l) ≤ C · l² / log l` for all large `l`. -/
axiom R3_upper_bound_aks :
    ∃ C : ℝ, C > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
      (Erdos1014OQ01.ramseyNumber 3 l : ℝ) ≤ C * (l : ℝ) ^ 2 / Real.log (l : ℝ)

/-- **Mattheus–Verstraëte (2024)** lower bound: there is a constant `c > 0`
    with `R(4, l) ≥ c · l³ / (log l)⁴` for all large `l`.  This is the recent
    determination of the order of magnitude of `R(4, l)`. -/
axiom R4_lower_bound_mv :
    ∃ c : ℝ, c > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
      (Erdos1014OQ01.ramseyNumber 4 l : ℝ) ≥ c * (l : ℝ) ^ 3 / (Real.log (l : ℝ)) ^ 4

-- ══════════════════════════════════════════════════════════════════
-- § Step 1: Increment bound from the Ramsey recurrence
-- ══════════════════════════════════════════════════════════════════

/-- The Ramsey recurrence `R(4, l+1) ≤ R(4, l) + R(3, l+1)` (the `k = 4`
    specialisation of the general recurrence proved in OQ-01). -/
theorem increment_bound_k4 (l : ℕ) (hl : l ≥ 1) :
    Erdos1014OQ01.ramseyNumber 4 (l + 1) ≤
      Erdos1014OQ01.ramseyNumber 4 l + Erdos1014OQ01.ramseyNumber 3 (l + 1) := by
  have h := Erdos1014OQ01.ramsey_recurrence 4 l (by norm_num) hl
  simpa using h

-- ══════════════════════════════════════════════════════════════════
-- § Step 2: Analysis lemma — (log l)⁴ / l → 0
-- ══════════════════════════════════════════════════════════════════

/-- `(x ^ (1/4)) ^ 4 = x` for `x ≥ 0`. -/
private lemma rpow_quarter_pow_four {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = x := by
  rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hx,
      show ((1 : ℝ) / 4) * ((4 : ℕ) : ℝ) = 1 by push_cast; ring, Real.rpow_one]

/-- `(log x)⁴ / x → 0` as `x → ∞`.  Proof: `log x =o[atTop] x^(1/4)`, raise to
    the 4th power to get `(log x)⁴ =o[atTop] (x^(1/4))⁴ = x`, then divide. -/
private lemma tendsto_log_pow_four_div_atTop :
    Tendsto (fun x : ℝ => (Real.log x) ^ 4 / x) atTop (𝓝 0) := by
  have hr : (0 : ℝ) < 1 / 4 := by norm_num
  have hlo : (fun x : ℝ => (Real.log x) ^ 4) =o[atTop]
      (fun x : ℝ => (x ^ ((1 : ℝ) / 4)) ^ 4) :=
    (isLittleO_log_rpow_atTop hr).pow (by norm_num)
  have htd := hlo.tendsto_div_nhds_zero
  refine htd.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [rpow_quarter_pow_four hx.le]

/-- For every `ε > 0`, eventually `(log l)⁴ / l < ε` (over natural `l`). -/
private lemma eventually_log4_div_small (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, ∀ l : ℕ, l > L → (Real.log (l : ℝ)) ^ 4 / (l : ℝ) < ε := by
  have hnat : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ 4 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_log_pow_four_div_atTop.comp tendsto_natCast_atTop_atTop
  have hev := hnat.eventually (Iio_mem_nhds hε)
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hev
  exact ⟨L, fun l hl => Set.mem_Iio.mp (hL l (le_of_lt hl))⟩

-- ══════════════════════════════════════════════════════════════════
-- § Main Theorem
-- ══════════════════════════════════════════════════════════════════

/-- **Erdős Problem #1014 for k = 4**: `R(4, l+1) / R(4, l) → 1` as `l → ∞`.

    Proved from the Ramsey recurrence together with the AKS upper bound on
    `R(3,·)` and the Mattheus–Verstraëte lower bound on `R(4,·)`. -/
theorem erdos_1014_k4_ratio_convergence :
    ∀ ε : ℝ, ε > 0 → ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
      |(Erdos1014OQ01.ramseyNumber 4 (l + 1) : ℝ) /
        (Erdos1014OQ01.ramseyNumber 4 l : ℝ) - 1| < ε := by
  intro ε hε
  obtain ⟨C, hC, L₁, hL₁⟩ := R3_upper_bound_aks
  obtain ⟨c, hc, L₂, hL₂⟩ := R4_lower_bound_mv
  obtain ⟨L₃, hL₃⟩ := eventually_log4_div_small (ε * c / (4 * C)) (by positivity)
  refine ⟨max (max (max L₁ L₂) L₃) 3, fun l hl => ?_⟩
  have hlL₁ : l > L₁ := by omega
  have hlL₂ : l > L₂ := by omega
  have hlL₃ : l > L₃ := by omega
  have hl4 : (4 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (show 4 ≤ l by omega)
  have hl_pos : (0 : ℝ) < (l : ℝ) := by linarith
  have hl_ge1 : l ≥ 1 := by omega
  have hlog_pos : 0 < Real.log (l : ℝ) := Real.log_pos (by linarith)
  set R := (Erdos1014OQ01.ramseyNumber 4 l : ℝ) with hR_def
  set R' := (Erdos1014OQ01.ramseyNumber 4 (l + 1) : ℝ) with hR'_def
  -- Positivity of the denominator R(4,l).
  have hR_pos : R > 0 := by
    simp only [hR_def]
    have := Erdos1014OQ01.ramsey_pos 4 l (by omega) hl_ge1
    exact_mod_cast (show 0 < Erdos1014OQ01.ramseyNumber 4 l by omega)
  -- Monotonicity R(4,l) ≤ R(4,l+1) makes the ratio ≥ 1.
  have hmon : R ≤ R' := by
    simp only [hR_def, hR'_def]
    exact_mod_cast Erdos1014OQ01.ramsey_monotone_right 4 l
  -- Increment: R' − R ≤ R(3, l+1).
  have hInc : R' - R ≤ (Erdos1014OQ01.ramseyNumber 3 (l + 1) : ℝ) := by
    simp only [hR_def, hR'_def]
    have h := increment_bound_k4 l hl_ge1
    have : (Erdos1014OQ01.ramseyNumber 4 (l + 1) : ℝ) ≤
        (Erdos1014OQ01.ramseyNumber 4 l : ℝ) +
          (Erdos1014OQ01.ramseyNumber 3 (l + 1) : ℝ) := by exact_mod_cast h
    linarith
  -- Numerator bound: R(3, l+1) ≤ 4·C·l² (AKS, then drop the log and the +1).
  have hlog1 : (1 : ℝ) ≤ Real.log ((l : ℝ) + 1) := by
    have hexp : Real.exp 1 ≤ (l : ℝ) + 1 := by
      have h9 := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log ((l : ℝ) + 1) := Real.log_le_log (Real.exp_pos 1) hexp
  have hNum : (Erdos1014OQ01.ramseyNumber 3 (l + 1) : ℝ) ≤ 4 * C * (l : ℝ) ^ 2 := by
    have hUB := hL₁ (l + 1) (by omega)
    -- hUB : R(3,l+1) ≤ C·(l+1)²/log(l+1)
    have hcast : ((l + 1 : ℕ) : ℝ) = (l : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hUB
    have hstep1 : C * ((l : ℝ) + 1) ^ 2 / Real.log ((l : ℝ) + 1) ≤
        C * ((l : ℝ) + 1) ^ 2 :=
      div_le_self (by positivity) hlog1
    have hstep2 : C * ((l : ℝ) + 1) ^ 2 ≤ 4 * C * (l : ℝ) ^ 2 := by
      have hsq : ((l : ℝ) + 1) ^ 2 ≤ 4 * (l : ℝ) ^ 2 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (l : ℝ) - 1)
          (by linarith : (0 : ℝ) ≤ 3 * (l : ℝ) + 1)]
      nlinarith [hsq, hC.le]
    linarith
  -- Denominator bound: R ≥ c·l³/(log l)⁴ > 0.
  have hDen : c * (l : ℝ) ^ 3 / (Real.log (l : ℝ)) ^ 4 ≤ R := by
    simp only [hR_def]; exact hL₂ l hlL₂
  have hDenPos : 0 < c * (l : ℝ) ^ 3 / (Real.log (l : ℝ)) ^ 4 := by
    apply div_pos (by positivity) (pow_pos hlog_pos 4)
  -- |R'/R − 1| = (R' − R)/R since R ≤ R' and R > 0.
  have habs : |R' / R - 1| = (R' - R) / R := by
    have h_eq : R' / R - 1 = (R' - R) / R := by field_simp
    rw [abs_of_nonneg]
    · exact h_eq
    · rw [h_eq]; exact div_nonneg (by linarith) (by linarith)
  rw [habs]
  -- Rewrite the target upper bound in the (log l)⁴/l shape.
  have hl_ne : (l : ℝ) ≠ 0 := ne_of_gt hl_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hC_ne : C ≠ 0 := ne_of_gt hC
  have hlog_ne : Real.log (l : ℝ) ≠ 0 := ne_of_gt hlog_pos
  have hcast_eq : (4 * C * (l : ℝ) ^ 2) / (c * (l : ℝ) ^ 3 / (Real.log (l : ℝ)) ^ 4)
      = (4 * C / c) * ((Real.log (l : ℝ)) ^ 4 / (l : ℝ)) := by
    rw [div_div_eq_mul_div]
    field_simp
    ring
  have hfac : (0 : ℝ) < 4 * C / c := by positivity
  calc (R' - R) / R
      ≤ (Erdos1014OQ01.ramseyNumber 3 (l + 1) : ℝ) / R :=
        div_le_div_of_nonneg_right hInc (le_of_lt hR_pos)
    _ ≤ (4 * C * (l : ℝ) ^ 2) / R :=
        div_le_div_of_nonneg_right hNum (le_of_lt hR_pos)
    _ ≤ (4 * C * (l : ℝ) ^ 2) / (c * (l : ℝ) ^ 3 / (Real.log (l : ℝ)) ^ 4) :=
        div_le_div_of_nonneg_left (by positivity) hDenPos hDen
    _ = (4 * C / c) * ((Real.log (l : ℝ)) ^ 4 / (l : ℝ)) := hcast_eq
    _ < (4 * C / c) * (ε * c / (4 * C)) :=
        mul_lt_mul_of_pos_left (hL₃ l hlL₃) hfac
    _ = ε := by field_simp; ring

end Erdos1014OQ04
