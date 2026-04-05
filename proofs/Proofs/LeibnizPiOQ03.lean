/-
# Leibniz Series Acceleration via Euler/Richardson Transforms (OQ-03)

The Leibniz series π/4 = 1 - 1/3 + 1/5 - ... converges at rate O(1/N).
This file formalizes two acceleration methods:

## Part I: Midpoint Acceleration

The midpoint M(k) = (S(2k) + S(2k+1)) / 2 satisfies:
  |M(k) - π/4| ≤ (S(2k+1) - S(2k))/2 = 1/(2·(4k+1))
This halves the error constant vs. the raw alternating series bound.

## Part II: Euler Transform (Geometric Convergence)

Key identity: for t ∈ [0,1], Σ_{n≥0} (1/2)^{n+1}(1-t²)^n = 1/(1+t²).
Integrating: Σ_{n≥0} (1/2)^{n+1} ∫₀¹(1-t²)^n dt = ∫₀¹ 1/(1+t²) dt = π/4.
The Euler series converges geometrically (each term ≤ (1/2)^{n+1}).

**Status**: Part I complete (0 sorries). Part II: 1 sorry (sum-integral exchange).
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace LeibnizPiOQ03

open Real Filter Finset BigOperators intervalIntegral MeasureTheory

-- ══════════════════════════════════════════════════════════════════
-- § Foundations (from LeibnizPiOQ01OQ01)
-- ══════════════════════════════════════════════════════════════════

noncomputable def S (n : ℕ) : ℝ :=
  ∑ k ∈ range n, ((-1 : ℝ) ^ k) / (2 * (k : ℝ) + 1)

theorem S_tendsto : Tendsto S atTop (nhds (π / 4)) :=
  Real.tendsto_sum_pi_div_four

theorem S_step (n : ℕ) : S (n + 1) - S n = (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) := by
  simp only [S, sum_range_succ]; ring

private theorem denom_pos (n : ℕ) : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity

private theorem neg_one_pow_even (k : ℕ) : (-1 : ℝ) ^ (2 * k) = 1 := by
  rw [pow_mul]; norm_num

private theorem neg_one_pow_odd (k : ℕ) : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
  rw [pow_add, neg_one_pow_even]; norm_num

private theorem even_mono : Monotone (fun k => S (2 * k)) := by
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
  have hle : 2 * (↑(2 * k) : ℝ) + 1 ≤ 2 * ↑(2 * k + 1) + 1 := by push_cast; linarith
  have hdiv := div_le_div_of_nonneg_left zero_le_one pos1 hle
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
  linarith

private theorem odd_anti : Antitone (fun k => S (2 * k + 1)) := by
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
  rw [show (2 : ℕ) * k + 1 + 1 = 2 * (k + 1) from by ring] at h1
  have pos1 : (0 : ℝ) < 2 * ↑(2 * k + 1) + 1 := denom_pos _
  have hle : 2 * (↑(2 * k + 1) : ℝ) + 1 ≤ 2 * ↑(2 * (k + 1)) + 1 := by push_cast; linarith
  have hdiv := div_le_div_of_nonneg_left zero_le_one pos1 hle
  linarith

private theorem even_tendsto : Tendsto (fun k => S (2 * k)) atTop (nhds (π / 4)) :=
  S_tendsto.comp (tendsto_atTop_atTop_of_monotone (fun a b h => by omega)
    (fun n => ⟨n, by omega⟩))

private theorem odd_tendsto : Tendsto (fun k => S (2 * k + 1)) atTop (nhds (π / 4)) :=
  S_tendsto.comp (tendsto_atTop_atTop_of_monotone (fun a b h => by omega)
    (fun n => ⟨n, by omega⟩))

theorem even_le_pi_div_4 (k : ℕ) : S (2 * k) ≤ π / 4 :=
  ge_of_tendsto even_tendsto (eventually_atTop.mpr ⟨k, fun _ hm => even_mono hm⟩)

theorem pi_div_4_le_odd (k : ℕ) : π / 4 ≤ S (2 * k + 1) :=
  le_of_tendsto odd_tendsto (eventually_atTop.mpr ⟨k, fun _ hm => odd_anti hm⟩)

-- ══════════════════════════════════════════════════════════════════
-- § Part I: Midpoint Acceleration
-- ══════════════════════════════════════════════════════════════════

noncomputable def midpoint (k : ℕ) : ℝ := (S (2 * k) + S (2 * k + 1)) / 2

theorem midpoint_tendsto : Tendsto midpoint atTop (nhds (π / 4)) := by
  unfold midpoint
  have h := even_tendsto.add odd_tendsto
  have := h.div_const 2
  simp only [show π / 4 + π / 4 = 2 * (π / 4) from by ring,
             mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] at this
  exact this

/-- The consecutive gap: S(2k+1) - S(2k) = 1/(4k+1). -/
theorem gap_eq (k : ℕ) : S (2 * k + 1) - S (2 * k) = 1 / (4 * (k : ℝ) + 1) := by
  have h := S_step (2 * k)
  rw [neg_one_pow_even k] at h
  convert h using 2
  push_cast; ring

/-- **Midpoint error bound**: |M(k) - π/4| ≤ 1/(2·(4k+1)). -/
theorem midpoint_error_bound (k : ℕ) :
    |midpoint k - π / 4| ≤ 1 / (2 * (4 * (k : ℝ) + 1)) := by
  unfold midpoint
  have hlo := even_le_pi_div_4 k
  have hhi := pi_div_4_le_odd k
  have hgap := gap_eq k
  -- Rewrite as error = (b-a)/2 where a = π/4-S(2k) ≥ 0 and b = S(2k+1)-π/4 ≥ 0
  rw [show (S (2 * k) + S (2 * k + 1)) / 2 - π / 4 =
      (S (2 * k + 1) - S (2 * k)) / 2 - (π / 4 - S (2 * k)) from by ring]
  rw [hgap, abs_le]
  have hd : (0:ℝ) < 4*(k:ℝ)+1 := by positivity
  have heq : (1:ℝ) / (4*(k:ℝ)+1) / 2 = 1/(2*(4*(k:ℝ)+1)) := by field_simp
  constructor <;> linarith

/-- **Midpoint improvement**: error ≤ half the bracket width. -/
theorem midpoint_vs_raw (k : ℕ) :
    |midpoint k - π / 4| ≤ (S (2 * k + 1) - S (2 * k)) / 2 := by
  unfold midpoint
  have hlo := even_le_pi_div_4 k
  have hhi := pi_div_4_le_odd k
  rw [show (S (2 * k) + S (2 * k + 1)) / 2 - π / 4 =
      (S (2 * k + 1) - S (2 * k)) / 2 - (π / 4 - S (2 * k)) from by ring]
  rw [abs_le]; constructor <;> linarith

-- ══════════════════════════════════════════════════════════════════
-- § Part II: Euler Transform — Geometric Convergence
-- ══════════════════════════════════════════════════════════════════

/-- **Geometric series identity**: for t ∈ [0,1],
    Σ_{n≥0} (1/2)^{n+1} · (1-t²)^n = 1/(1+t²). -/
theorem geometric_series_eq (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    HasSum (fun n => (1 / 2 : ℝ) ^ (n + 1) * (1 - t ^ 2) ^ n) (1 / (1 + t ^ 2)) := by
  have hr0 : 0 ≤ (1 - t ^ 2) / 2 := by nlinarith [sq_nonneg t]
  have hr1 : (1 - t ^ 2) / 2 < 1 := by nlinarith [sq_nonneg t]
  have hgeom := hasSum_geometric_of_lt_one hr0 hr1
  have ht2 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  -- (1/2)^{n+1} * (1-t²)^n = (1/2) * ((1-t²)/2)^n
  have key : ∀ n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * (1 - t ^ 2) ^ n =
      (1 / 2) * ((1 - t ^ 2) / 2) ^ n := by
    intro n
    rw [pow_succ, mul_comm ((1/2:ℝ)^n) (1/2), mul_assoc, ← mul_pow,
        show (1/2:ℝ) * (1 - t^2) = (1 - t^2) / 2 from by ring]
  simp_rw [key]
  -- Sum = (1/2) * (1-(1-t²)/2)⁻¹ = 1/(1+t²)
  rw [show (1 : ℝ) / (1 + t ^ 2) = (1 / 2) * (1 - (1 - t ^ 2) / 2)⁻¹ from by
    have h1 : (1:ℝ) - (1-t^2)/2 = (1+t^2)/2 := by ring
    rw [h1, inv_div]; ring]
  exact hgeom.mul_left (1 / 2)

/-- Each (1-t²)^n ≤ 1 for t ∈ [0,1]. -/
theorem one_sub_sq_pow_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    (1 - t ^ 2) ^ n ≤ 1 :=
  pow_le_one₀ (by nlinarith [sq_nonneg t]) (by nlinarith [sq_nonneg t])

/-- ∫₀¹(1-t²)^n dt ≥ 0. -/
theorem euler_integral_nonneg (n : ℕ) :
    0 ≤ ∫ t in (0 : ℝ)..1, (1 - t ^ 2) ^ n :=
  intervalIntegral.integral_nonneg (by norm_num)
    (fun x hx => pow_nonneg (by nlinarith [hx.1, hx.2]) n)

/-- Each Euler term: (1/2)^{n+1} · ∫₀¹(1-t²)^n dt ≤ (1/2)^{n+1}. -/
theorem euler_term_le (n : ℕ) :
    (1 / 2 : ℝ) ^ (n + 1) * ∫ t in (0 : ℝ)..1, (1 - t ^ 2) ^ n ≤ (1 / 2) ^ (n + 1) := by
  apply mul_le_of_le_one_right (pow_nonneg (by norm_num) _)
  have h : ∫ t in (0:ℝ)..1, (1 - t^2)^n ≤ ∫ t in (0:ℝ)..1, (1:ℝ) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact ((continuous_const.sub (continuous_id.pow 2)).pow n).intervalIntegrable 0 1
    · exact continuous_const.intervalIntegrable 0 1
    · intro x hx; exact one_sub_sq_pow_le x hx.1 hx.2 n
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at h
  linarith

/-- The Euler series is **summable**: each term ≤ (1/2)^{n+1} (geometric). -/
theorem euler_summable :
    Summable (fun n => (1 / 2 : ℝ) ^ (n + 1) * ∫ t in (0 : ℝ)..1, (1 - t ^ 2) ^ n) := by
  apply Summable.of_nonneg_of_le
  · intro n; exact mul_nonneg (pow_nonneg (by norm_num) _) (euler_integral_nonneg n)
  · exact euler_term_le
  · apply Summable.congr
      ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).mul_left (1/2 : ℝ))
    intro n
    rw [mul_comm, ← pow_succ]

/-- The integral ∫₀¹ 1/(1+t²) dt = π/4 (via arctan FTC). -/
theorem arctan_integral : ∫ t in (0 : ℝ)..1, 1 / (1 + t ^ 2) = π / 4 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t => arctan t) (1 / (1 + x ^ 2)) x :=
    fun x _ => hasDerivAt_arctan x
  have hint : IntervalIntegrable (fun t => 1 / (1 + t ^ 2)) volume 0 1 :=
    ((continuous_const.div
      (continuous_const.add (continuous_id.pow 2))
      (fun x => by positivity)).continuousOn).intervalIntegrable
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [arctan_one, arctan_zero]

/-- **The Euler Transform Identity** (1 sorry): π/4 = Σ (1/2)^{n+1} ∫₀¹(1-t²)^n dt.

    The exchange of Σ and ∫ is justified by dominated convergence:
    (1/2)^{n+1}(1-t²)^n ≤ (1/2)^{n+1} uniformly, with summable dominating function. -/
theorem euler_transform_eq :
    ∑' n, ((1 / 2 : ℝ) ^ (n + 1) * ∫ t in (0 : ℝ)..1, (1 - t ^ 2) ^ n) = π / 4 := by
  sorry -- Requires: MeasureTheory.integral_tsum + dominated convergence

end LeibnizPiOQ03
