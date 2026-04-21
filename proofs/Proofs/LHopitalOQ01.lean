/-
  L'Hôpital's Rule: Failure of the Converse
  Open Question: lhopital-oq-01

  The converse of L'Hôpital's rule fails: the existence of lim f(x)/g(x)
  does NOT imply that lim f'(x)/g'(x) exists.

  Counterexample:
    f(x) = x + sin x,   g(x) = x
    f'(x) = 1 + cos x,  g'(x) = 1

  Proved:
  1. f'(x)/g'(x) = 1 + cos(x)              [derivative computation]
  2. lim_{x→∞} f(x)/g(x) = 1               [limit exists via sin(x)/x → 0]
  3. lim_{x→∞} f'(x)/g'(x) does not exist  [oscillates between 0 and 2]

  This is the canonical example showing that L'Hôpital's rule is a one-directional tool:
  the rule allows computing the limit of f/g FROM the limit of f'/g',
  but knowing f/g has a limit gives no information about f'/g'.

  References:
  - LHopital.lean: base L'Hôpital's rule (Wiedijk #64)
  - Rudin, Principles of Mathematical Analysis, §5.13
-/

import Mathlib

namespace LHopitalFailure

open Real Filter Topology

-- ============================================================
-- §1. Derivatives of f and g
-- ============================================================

/-- f(x) = x + sin(x) has derivative 1 + cos(x) everywhere. -/
theorem f_hasDerivAt (x : ℝ) :
    HasDerivAt (fun x => x + Real.sin x) (1 + Real.cos x) x :=
  (hasDerivAt_id x).add (Real.hasDerivAt_sin x)

/-- g(x) = x has derivative 1 everywhere. -/
theorem g_hasDerivAt (x : ℝ) :
    HasDerivAt id (1 : ℝ) x :=
  hasDerivAt_id x

/-- The ratio of derivatives simplifies to 1 + cos(x). -/
theorem deriv_ratio_eq (x : ℝ) :
    (1 + Real.cos x) / 1 = 1 + Real.cos x := div_one _

-- ============================================================
-- §2. The limit f(x)/g(x) → 1 as x → ∞
-- ============================================================

/-- sin(x)/x → 0 as x → ∞, proved via squeeze using the bound from 1/x → 0. -/
theorem sin_div_tendsto_zero :
    Tendsto (fun x : ℝ => Real.sin x / x) atTop (nhds 0) := by
  -- Key: |sin x / x| ≤ 1/x = x⁻¹, and x⁻¹ → 0
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  rw [Metric.tendsto_atTop] at hinv ⊢
  intro ε hε
  obtain ⟨M, hM⟩ := hinv ε hε
  exact ⟨max M 1, fun x hx => by
    have hxM : M ≤ x := (le_max_left M 1).trans hx
    have hx1 : 1 ≤ x := (le_max_right M 1).trans hx
    have hx_pos : (0 : ℝ) < x := by linarith
    -- x⁻¹ < ε from the bound on tendsto_inv_atTop_zero
    have hbnd : x⁻¹ < ε := by
      have := hM x hxM
      rwa [Real.dist_eq, sub_zero, abs_of_pos (inv_pos.mpr hx_pos)] at this
    rw [Real.dist_eq, sub_zero]
    have hsin_abs : |Real.sin x| ≤ 1 :=
      abs_le.mpr ⟨by linarith [Real.neg_one_le_sin x], Real.sin_le_one x⟩
    calc |Real.sin x / x|
        = |Real.sin x| / x := by rw [abs_div, abs_of_pos hx_pos]
      _ ≤ 1 / x := by gcongr
      _ = x⁻¹ := one_div x
      _ < ε := hbnd⟩

/-- (x + sin x)/x → 1 as x → ∞, by writing it as 1 + sin(x)/x and applying the squeeze. -/
theorem f_div_g_tendsto_one :
    Tendsto (fun x : ℝ => (x + Real.sin x) / x) atTop (nhds 1) := by
  -- The two functions agree eventually (for x ≥ 1 ≠ 0)
  have heq : ∀ᶠ x : ℝ in atTop, (x + Real.sin x) / x = 1 + Real.sin x / x := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    field_simp [show x ≠ 0 from by linarith]
  -- 1 + sin x/x → 1 + 0 = 1
  have h1 : Tendsto (fun x : ℝ => 1 + Real.sin x / x) atTop (nhds 1) := by
    have h := (show Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) from tendsto_const_nhds).add
              sin_div_tendsto_zero
    simpa using h
  exact h1.congr' (heq.mono fun x h => h.symm)

-- ============================================================
-- §3. The ratio of derivatives does not converge
-- ============================================================

/-- cos(2πn) = 1 for all n : ℕ, using the integer multiple periodicity formula. -/
theorem cos_two_pi_nat (n : ℕ) : Real.cos (2 * Real.pi * (n : ℝ)) = 1 := by
  rw [show 2 * Real.pi * (n : ℝ) = (n : ℤ) * (2 * Real.pi) from by push_cast; ring]
  exact Real.cos_int_mul_two_pi n

/-- cos(π + 2πn) = -1 for all n : ℕ.
    Proof: π + 2πn = 2πn + π, use cos(x + π) = -cos(x), then cos(2πn) = 1. -/
theorem cos_pi_add_two_pi_nat (n : ℕ) : Real.cos (Real.pi + 2 * Real.pi * (n : ℝ)) = -1 := by
  rw [show Real.pi + 2 * Real.pi * (n : ℝ) = 2 * Real.pi * (n : ℝ) + Real.pi from by ring]
  rw [Real.cos_add_pi]
  simp [cos_two_pi_nat n]

/-- 2πn → ∞ as n → ∞, since n → ∞ and 2π > 0. -/
theorem two_pi_nat_atTop :
    Tendsto (fun n : ℕ => 2 * Real.pi * (n : ℝ)) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp tendsto_natCast_atTop_atTop) (b / (2 * Real.pi))
  exact ⟨N, fun n hn => by
    have hb := hN n hn
    calc b = 2 * Real.pi * (b / (2 * Real.pi)) := by field_simp [Real.two_pi_pos.ne']
      _ ≤ 2 * Real.pi * n := mul_le_mul_of_nonneg_left hb Real.two_pi_pos.le⟩

/-- π + 2πn → ∞ as n → ∞, since 2πn → ∞ and the constant π doesn't hurt. -/
theorem pi_add_two_pi_nat_atTop :
    Tendsto (fun n : ℕ => Real.pi + 2 * Real.pi * (n : ℝ)) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp two_pi_nat_atTop (b - Real.pi)
  exact ⟨N, fun n hn => by linarith [hN n hn, Real.pi_pos]⟩

/-- 1 + cos(x) does not converge to any limit as x → ∞.
    Proof: at x = 2πn it equals 2, at x = π + 2πn it equals 0.
    Any limit L satisfies L = 2 (from first subsequence) and L = 0 (from second). -/
theorem deriv_ratio_no_limit :
    ¬∃ L : ℝ, Tendsto (fun x : ℝ => 1 + Real.cos x) atTop (nhds L) := by
  intro ⟨L, hL⟩
  -- Subsequence along 2πn → ∞: value is 2 at each point
  have h_along_2pi :
      Tendsto (fun n : ℕ => 1 + Real.cos (2 * Real.pi * (n : ℝ))) atTop (nhds L) :=
    hL.comp two_pi_nat_atTop
  have hval2 : ∀ n : ℕ, 1 + Real.cos (2 * Real.pi * (n : ℝ)) = 2 := by
    intro n; rw [cos_two_pi_nat n]; norm_num
  simp_rw [hval2] at h_along_2pi
  have hL2 : L = 2 :=
    tendsto_nhds_unique h_along_2pi tendsto_const_nhds
  -- Subsequence along π + 2πn → ∞: value is 0 at each point
  have h_along_pi :
      Tendsto (fun n : ℕ => 1 + Real.cos (Real.pi + 2 * Real.pi * (n : ℝ))) atTop (nhds L) :=
    hL.comp pi_add_two_pi_nat_atTop
  have hval0 : ∀ n : ℕ, 1 + Real.cos (Real.pi + 2 * Real.pi * (n : ℝ)) = 0 := by
    intro n; rw [cos_pi_add_two_pi_nat n]; norm_num
  simp_rw [hval0] at h_along_pi
  have hL0 : L = 0 :=
    tendsto_nhds_unique h_along_pi tendsto_const_nhds
  -- L = 2 and L = 0 is a contradiction
  linarith

-- ============================================================
-- §4. The Failure Statement
-- ============================================================

/-- L'Hôpital's rule failure: (x + sin x)/x → 1 but the ratio of derivatives
    (1 + cos x)/1 = 1 + cos x has no limit. This shows L'Hôpital's rule is
    one-directional: f'/g' → L implies f/g → L, but NOT conversely. -/
theorem lhopital_failure :
    (Tendsto (fun x : ℝ => (x + Real.sin x) / x) atTop (nhds 1)) ∧
    (¬∃ L : ℝ, Tendsto (fun x : ℝ => (1 + Real.cos x) / 1) atTop (nhds L)) :=
  ⟨f_div_g_tendsto_one, by
    simp only [div_one]
    exact deriv_ratio_no_limit⟩

end LHopitalFailure
