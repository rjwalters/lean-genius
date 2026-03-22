import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Tactic
import Mathlib.Order.Monotone.Basic

/-
  Optimal Convergence Rate for Arctangent-Based Pi Series (OQ-01)

  The Leibniz series π/4 = Σ (-1)^n/(2n+1) converges at rate Θ(1/N).
  We prove |π/4 - Sₙ| ≤ 1/(2N+1) and show the rate is sharp.
  Machin-type formulas achieve exponential O(1/m^(2N)) rates instead.
-/

namespace LeibnizPiOQ01

open Finset BigOperators Filter Real

set_option maxHeartbeats 800000

noncomputable def S (n : ℕ) : ℝ :=
  ∑ i ∈ range n, ((-1 : ℝ) ^ i) / (2 * ↑i + 1)

theorem S_tendsto : Tendsto S atTop (nhds (π / 4)) :=
  Real.tendsto_sum_pi_div_four

theorem S_step (n : ℕ) :
    S (n + 1) - S n = (-1 : ℝ) ^ n / (2 * ↑n + 1) := by
  simp only [S, sum_range_succ]; ring

theorem denom_pos (n : ℕ) : (0 : ℝ) < 2 * ↑n + 1 := by positivity

theorem neg_one_pow_even (k : ℕ) : (-1 : ℝ) ^ (2 * k) = 1 := by
  rw [pow_mul, neg_one_sq, one_pow]

theorem neg_one_pow_odd (k : ℕ) : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
  rw [pow_add, neg_one_pow_even, one_mul, pow_one]

theorem even_mono : Monotone (fun k => S (2 * k)) := by
  apply monotone_nat_of_le_succ
  intro k
  show S (2 * k) ≤ S (2 * (k + 1))
  have h1 := S_step (2 * k)
  have h2 := S_step (2 * k + 1)
  rw [neg_one_pow_even k] at h1
  rw [neg_one_pow_odd k] at h2
  have h_neg : (-1 : ℝ) / (2 * ↑(2 * k + 1) + 1) =
    -(1 / (2 * ↑(2 * k + 1) + 1)) := by ring
  rw [h_neg] at h2
  have pos1 : (0 : ℝ) < 2 * ↑(2 * k) + 1 := denom_pos _
  have hle : 2 * (↑(2 * k) : ℝ) + 1 ≤ 2 * ↑(2 * k + 1) + 1 := by
    push_cast; linarith
  have hdiv := div_le_div_of_nonneg_left zero_le_one pos1 hle
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
  linarith

theorem odd_anti : Antitone (fun k => S (2 * k + 1)) := by
  apply antitone_nat_of_succ_le
  intro k
  show S (2 * (k + 1) + 1) ≤ S (2 * k + 1)
  have h1 := S_step (2 * k + 1)
  have h2 := S_step (2 * k + 2)
  rw [neg_one_pow_odd k] at h1
  have h_neg : (-1 : ℝ) / (2 * ↑(2 * k + 1) + 1) =
    -(1 / (2 * ↑(2 * k + 1) + 1)) := by ring
  rw [h_neg] at h1
  rw [show (2 : ℕ) * k + 2 = 2 * (k + 1) from by ring] at h2
  rw [neg_one_pow_even (k + 1)] at h2
  -- Normalize h1 to use S(2*(k+1)) instead of S(2*k+1+1)
  rw [show (2 : ℕ) * k + 1 + 1 = 2 * (k + 1) from by ring] at h1
  have pos1 : (0 : ℝ) < 2 * ↑(2 * k + 1) + 1 := denom_pos _
  have hle : 2 * (↑(2 * k + 1) : ℝ) + 1 ≤ 2 * ↑(2 * (k + 1)) + 1 := by
    push_cast; linarith
  have hdiv := div_le_div_of_nonneg_left zero_le_one pos1 hle
  linarith

theorem even_tendsto : Tendsto (fun k => S (2 * k)) atTop (nhds (π / 4)) :=
  S_tendsto.comp (tendsto_atTop_atTop_of_monotone
    (fun a b h => by omega) (fun n => ⟨n, by omega⟩))

theorem odd_tendsto : Tendsto (fun k => S (2 * k + 1)) atTop (nhds (π / 4)) :=
  S_tendsto.comp (tendsto_atTop_atTop_of_monotone
    (fun a b h => by omega) (fun n => ⟨n, by omega⟩))

theorem even_le_pi_div_4 (k : ℕ) : S (2 * k) ≤ π / 4 :=
  ge_of_tendsto even_tendsto (eventually_atTop.mpr
    ⟨k, fun _ hm => even_mono hm⟩)

theorem pi_div_4_le_odd (k : ℕ) : π / 4 ≤ S (2 * k + 1) :=
  le_of_tendsto odd_tendsto (eventually_atTop.mpr
    ⟨k, fun _ hm => odd_anti hm⟩)

/-- **Error bound for the Leibniz series.**
    |π/4 - S(n)| ≤ 1/(2n+1). This is the alternating series estimation theorem. -/
theorem error_bound (n : ℕ) :
    |π / 4 - S n| ≤ 1 / (2 * ↑n + 1) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- Even: n = k + k
    have hn : n = 2 * k := by omega
    subst hn
    have hlo := even_le_pi_div_4 k
    have hhi := pi_div_4_le_odd k
    have h_step := S_step (2 * k)
    rw [neg_one_pow_even k] at h_step
    rw [abs_of_nonneg (by linarith)]
    -- π/4 ≤ S(2k+1) = S(2k) + 1/(4k+1), so π/4 - S(2k) ≤ 1/(4k+1)
    linarith
  · -- Odd: n = 2*k + 1
    subst hk
    have hhi := pi_div_4_le_odd k
    have hlo := even_le_pi_div_4 (k + 1)
    have h_step := S_step (2 * k + 1)
    rw [neg_one_pow_odd k] at h_step
    have h_neg : (-1 : ℝ) / (2 * ↑(2 * k + 1) + 1) =
      -(1 / (2 * ↑(2 * k + 1) + 1)) := by ring
    rw [h_neg] at h_step
    rw [abs_of_nonpos (by linarith)]
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring] at hlo
    linarith

/-- Sharpness: consecutive terms differ by exactly 1/(2n+1). -/
theorem rate_sharp (n : ℕ) :
    |S (n + 1) - S n| = 1 / (2 * ↑n + 1) := by
  rw [S_step]
  rw [abs_div, abs_of_pos (denom_pos n)]
  congr 1
  simp [abs_pow, abs_neg, abs_one]

theorem machin_formula :
    4 * arctan (1 / 5 : ℝ) - arctan (1 / 239 : ℝ) = π / 4 := by
  simp only [one_div]
  exact four_mul_arctan_inv_5_sub_arctan_inv_239

end LeibnizPiOQ01
