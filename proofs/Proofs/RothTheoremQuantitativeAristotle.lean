/-
  Aristotle targets for Roth's Theorem Quantitative Bounds
  Supporting analysis and density lemmas for automated proof search.
  See RothTheoremQuantitative.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main quantitative bounds (Roth, Behrend, Kelley-Meka)
  - Routine arithmetic and analytic facts about density and AP-free sets
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace RothTheoremQuantitativeAristotle

open Real Finset Filter

-- ═══════════════════════════════════════════════════════════════════
-- PART I: Density Arithmetic
-- ═══════════════════════════════════════════════════════════════════

/-- If δ > 0, then δ² > 0. -/
theorem delta_sq_pos (delta : ℝ) (hdelta : 0 < delta) : 0 < delta ^ 2 := by
  positivity

/-- If δ > 0, then 100 / δ² > 0. -/
theorem density_bound_pos (delta : ℝ) (hdelta : 0 < delta) : 0 < 100 / delta ^ 2 := by
  positivity

/-- The density increment formula: δ + k * δ² / 100 is increasing in k. -/
theorem density_increment_mono (delta : ℝ) (hdelta : 0 < delta) (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) :
    delta + k₁ * delta ^ 2 / 100 ≤ delta + k₂ * delta ^ 2 / 100 := by
  gcongr
  exact_mod_cast h

/-- After at most ⌊100/δ²⌋ density increments, the density exceeds 1. -/
theorem density_exceeds_one_after_floor (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ k : ℕ, k ≤ ⌊100 / delta ^ 2⌋₊ + 1 ∧ delta + k * delta ^ 2 / 100 > 1 := by
  refine ⟨⌊100 / delta ^ 2⌋₊ + 1, le_refl _, ?_⟩
  have hd2 : 0 < delta ^ 2 := by positivity
  have hk : (100 / delta ^ 2 : ℝ) < (⌊100 / delta ^ 2⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  push_cast
  nlinarith [sq_nonneg delta]

/-- The Roth iteration count ⌊100/δ²⌋ is monotone: smaller δ gives more iterations. -/
theorem iteration_count_antimono (delta₁ delta₂ : ℝ) (h₁ : 0 < delta₁) (h₂ : 0 < delta₂)
    (h : delta₁ ≤ delta₂) : ⌊100 / delta₂ ^ 2⌋₊ ≤ ⌊100 / delta₁ ^ 2⌋₊ := by
  apply Nat.floor_le_floor
  have hsq : delta₁ ^ 2 ≤ delta₂ ^ 2 := by nlinarith [sq_nonneg (delta₂ - delta₁)]
  exact div_le_div_of_le_left (by positivity) (by positivity) hsq

/-- For δ = 1/√(log N), 100/δ² = 100 * log N. -/
theorem roth_iteration_count_formula (N : ℕ) (hN : 2 < N) :
    100 / (1 / sqrt (log N)) ^ 2 = 100 * log N := by
  have hlogN : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsqrt : sqrt (log N) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlogN)
  rw [div_pow, one_pow, sq_sqrt hlogN.le]
  field_simp

-- ═══════════════════════════════════════════════════════════════════
-- PART II: AP-Freeness Properties
-- ═══════════════════════════════════════════════════════════════════

/-- AP-freeness is closed under taking subsets (in ZMod N). -/
theorem apFree_mono {N : ℕ} {A B : Finset (ZMod N)}
    (hAB : B ⊆ A)
    (hA : ∀ a d : ZMod N, d ≠ 0 → a ∈ A → a + d ∈ A → a + 2 * d ∉ A) :
    ∀ a d : ZMod N, d ≠ 0 → a ∈ B → a + d ∈ B → a + 2 * d ∉ B :=
  fun a d hd ha had hadd => hA a d hd (hAB ha) (hAB had) (hAB hadd)

/-- A 2-element AP-free set: {0, 1} in ZMod N for N ≥ 3.

    Proof: If a, a+d ∈ {0,1} with d ≠ 0:
    - a=0, d=1: a+2d=2. Since N≥3, val(2)=2≠0,1, so 2∉{0,1}.
    - a=1, d=-1: a+2d=-1. val(-1)=N-1≥2≠0,1, so -1∉{0,1}. -/
theorem two_element_ap_free (N : ℕ) (hN : 3 ≤ N) :
    ∀ a d : ZMod N, d ≠ 0 → a ∈ ({0, 1} : Finset (ZMod N)) →
    a + d ∈ ({0, 1} : Finset (ZMod N)) → a + 2 * d ∉ ({0, 1} : Finset (ZMod N)) := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : Nontrivial (ZMod N) := ZMod.instNontrivial (by omega)
  -- Val computation helpers
  have hv2 : (2 : ZMod N).val = 2 := by
    show ((2 : ℕ) : ZMod N).val = 2
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hv_neg1 : (-1 : ZMod N).val = N - 1 := ZMod.val_neg_one' (by omega)
  have hv0 : (0 : ZMod N).val = 0 := ZMod.val_zero N
  have hv1 : (1 : ZMod N).val = 1 := by
    show ((1 : ℕ) : ZMod N).val = 1
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  -- Use val injectivity to prove distinctness
  have val_inj : ∀ x y : ZMod N, x = y → x.val = y.val := congr_arg ZMod.val
  have h2ne0 : (2 : ZMod N) ≠ 0 :=
    fun h => by have := val_inj _ _ h; rw [hv2, hv0] at this; omega
  have h2ne1 : (2 : ZMod N) ≠ 1 :=
    fun h => by have := val_inj _ _ h; rw [hv2, hv1] at this; omega
  have hn1ne0 : (-1 : ZMod N) ≠ 0 :=
    fun h => by have := val_inj _ _ h; rw [hv_neg1, hv0] at this; omega
  have hn1ne1 : (-1 : ZMod N) ≠ 1 :=
    fun h => by have := val_inj _ _ h; rw [hv_neg1, hv1] at this; omega
  intro a d hd ha had
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha had
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  rcases ha with rfl | rfl <;> rcases had with h | h
  · -- a=0, a+d=0 → d=0, contradiction
    simp only [zero_add] at h; exact absurd h hd
  · -- a=0, a+d=1 → d=1, a+2d=2
    simp only [zero_add] at h; subst h
    simp only [zero_add, mul_one]
    exact ⟨h2ne0, h2ne1⟩
  · -- a=1, a+d=0 → d=-1, a+2d = 1 + 2*(-1) = -1
    have hd_eq : d = -1 := by linear_combination h
    subst hd_eq
    have h_simp : (1 : ZMod N) + 2 * (-1) = -1 := by ring
    rw [h_simp]
    exact ⟨hn1ne0, hn1ne1⟩
  · -- a=1, a+d=1 → d=0, contradiction
    have hd_eq : d = 0 := by linear_combination h
    exact absurd hd_eq hd

-- NOTE: rothNumber_ge_half (r₃(N) ≥ ⌊N/2⌋) was REMOVED — it is FALSE for large N.
-- By Roth's theorem, r₃(N)/N → 0, so r₃(N) < N/2 for sufficiently large N.

-- ═══════════════════════════════════════════════════════════════════
-- PART III: Logarithmic Growth Facts
-- ═══════════════════════════════════════════════════════════════════

/-- log N → ∞ as N → ∞. -/
theorem log_nat_tendsto_atTop :
    Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- For N ≥ 3, log(log N) > 0. -/
theorem log_log_pos (N : ℕ) (hN : 3 ≤ N) : 0 < Real.log (Real.log N) := by
  have hN_real : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hN1 : 1 < Real.log N := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le he hN_real)
  exact Real.log_pos hN1

/-- N / log(log N) → ∞ as N → ∞.

    Proof sketch: eventually log(log N) ≤ log N ≤ √N (by isLittleO_log_rpow_atTop),
    so N/log(log N) ≥ N/√N = √N → ∞.

    The formal Lean proof requires careful assembly of:
    (1) log N ≤ √N eventually: from isLittleO_log_rpow_atTop (ε=1/2)
    (2) log(log N) ≤ log N: from Real.log_le_log when log N ≥ 1
    (3) log(log N) > 0 eventually: from log_log_pos when N ≥ 3
    (4) N/log(log N) ≥ N/√N = √N: from div_le_div_left
    (5) √N → ∞: Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop -/
theorem n_div_log_log_tendsto_atTop :
    Tendsto (fun N : ℕ => (N : ℝ) / Real.log (Real.log N)) atTop atTop := by
  -- Use isLittleO to get log N ≤ √N eventually
  have h_logN_le_sqrtN : ∀ᶠ N : ℕ in atTop, Real.log N ≤ Real.sqrt N := by
    have h_isLittleO := isLittleO_log_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)
    have h_bound := h_isLittleO.bound (show (0:ℝ) < 1 by norm_num)
    have h_real : ∀ᶠ x : ℝ in atTop, Real.log x ≤ Real.sqrt x := by
      filter_upwards [h_bound, Filter.eventually_ge_atTop (1:ℝ)] with x hx hx1
      have h_log_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
      simp only [one_mul, Real.norm_eq_abs, abs_of_nonneg h_log_nn, Real.sqrt_eq_rpow] at hx
      exact hx
    exact tendsto_natCast_atTop_atTop.eventually h_real
  -- Squeeze: N/log(log N) ≥ √N → ∞
  rw [tendsto_atTop_atTop]
  intro K
  -- Need: eventually K ≤ N / log(log N)
  -- Use: eventually K ≤ √N and √N ≤ N / log(log N)
  have h_sqrt_lb := (Real.tendsto_sqrt_atTop.comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  filter_upwards [h_logN_le_sqrtN, h_sqrt_lb,
      Filter.eventually_ge_atTop (3 : ℕ)] with N h_logN_sqrt h_sqrt_K hN3
  have hN3' : 3 ≤ N := hN3
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (by omega : N ≠ 0)
  have h_logN_pos : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have h_loglogN_pos : 0 < Real.log (Real.log N) := log_log_pos N hN3'
  have h_loglogN_le_sqrtN : Real.log (Real.log N) ≤ Real.sqrt N :=
    (Real.log_le_log h_logN_pos h_logN_sqrt).trans h_logN_sqrt
  -- √N ≤ N / log(log N) since log(log N) ≤ √N and log(log N) > 0
  have h_sqrtN_le_div : Real.sqrt N ≤ N / Real.log (Real.log N) := by
    rw [le_div_iff h_loglogN_pos]
    calc Real.sqrt N * Real.log (Real.log N)
        ≤ Real.sqrt N * Real.sqrt N := mul_le_mul_of_nonneg_left h_loglogN_le_sqrtN
              (Real.sqrt_nonneg _)
      _ = N := Real.mul_self_sqrt hNpos.le
  linarith

/-- For c > 0, N · exp(-c · √(log N)) is eventually greater than any constant.

    Proof: eventually c*√(log N) ≤ (log N)/2 (when √(log N) ≥ 2c, i.e., log N ≥ 4c²).
    Then exp(-c√log N) ≥ exp(-log N/2) = 1/√N, so N*exp(-c√log N) ≥ √N → ∞. -/
theorem behrend_lower_eventually_large (c : ℝ) (hc : 0 < c) (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, K < N * Real.exp (-c * Real.sqrt (Real.log N)) := by
  -- Eventually: log N ≥ 4c² (so √(log N) ≥ 2c) and √N ≥ K
  have h_log_lb := log_nat_tendsto_atTop.eventually_ge_atTop (4 * c ^ 2)
  have h_sqrt_lb := (Real.tendsto_sqrt_atTop.comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (max K 1)
  have h_Npos : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < N :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop 0
  filter_upwards [h_log_lb, h_sqrt_lb, h_Npos] with N h_log h_sqrt hNpos
  have h_logN_pos : 0 < Real.log N := by linarith [sq_nonneg c]
  -- √(log N) ≥ 2c
  have h_sqrt_log : 2 * c ≤ Real.sqrt (Real.log N) := by
    rw [← Real.sqrt_sq (by linarith : 0 ≤ 2 * c)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  -- c * √(log N) ≤ (log N)/2
  have h_c_sqrt_le : c * Real.sqrt (Real.log N) ≤ Real.log N / 2 := by
    have hsqpos : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr h_logN_pos
    nlinarith [Real.mul_self_sqrt h_logN_pos.le, h_sqrt_log, Real.sqrt_nonneg (Real.log N)]
  -- exp(-c√log N) ≥ exp(-log N/2)
  have h_exp_lb : Real.exp (-Real.log N / 2) ≤ Real.exp (-c * Real.sqrt (Real.log N)) :=
    Real.exp_le_exp.mpr (by linarith)
  -- exp(-log N / 2) = 1/√N (since log N = 2*log(√N))
  have hNpos_r : (0 : ℝ) < N := hNpos
  have h_sqrt_N_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos_r
  have h_exp_eq : Real.exp (-Real.log N / 2) = 1 / Real.sqrt N := by
    rw [show -Real.log N / 2 = -Real.log (Real.sqrt N) from by
        rw [Real.log_sqrt hNpos_r.le]; ring]
    rw [Real.exp_neg, Real.exp_log h_sqrt_N_pos]
  -- N * (1/√N) = √N
  have h_N_sqrt : N * (1 / Real.sqrt N) = Real.sqrt N := by
    field_simp [ne_of_gt h_sqrt_N_pos]
    exact Real.mul_self_sqrt hNpos_r.le
  -- Put it together
  calc K ≤ Real.sqrt N := le_of_max_le_left h_sqrt
    _ = N * (1 / Real.sqrt N) := h_N_sqrt.symm
    _ = N * Real.exp (-Real.log N / 2) := by rw [← h_exp_eq]
    _ ≤ N * Real.exp (-c * Real.sqrt (Real.log N)) := by
        gcongr; exact h_exp_lb

/-- The Behrend exponent satisfies: exp(-c√(log N)) ≥ N^(-ε) eventually.

    Proof: need ε * log N ≥ c * √(log N), i.e., ε√(log N) ≥ c.
    For large N: log N ≥ (c/ε)², so √(log N) ≥ c/ε, so ε√(log N) ≥ c. -/
theorem behrend_exponent_vs_poly (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.exp (-c * Real.sqrt (Real.log N)) ≥ (N : ℝ) ^ (-ε) := by
  -- Eventually: log N ≥ (c/ε)²
  have h_log_lb := log_nat_tendsto_atTop.eventually_ge_atTop ((c / ε) ^ 2)
  have h_Npos : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < N :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop 0
  filter_upwards [h_log_lb, h_Npos] with N h_log hNpos
  have h_logN_pos : 0 < Real.log N := by
    calc 0 ≤ (c / ε) ^ 2 := sq_nonneg _
      _ ≤ Real.log N := h_log
  -- √(log N) ≥ c/ε
  have h_sqrt_lb : c / ε ≤ Real.sqrt (Real.log N) := by
    have hce : 0 ≤ c / ε := le_of_lt (div_pos hc hε)
    rw [← Real.sqrt_sq hce]
    exact Real.sqrt_le_sqrt h_log
  -- ε * √(log N) ≥ c
  have h_eps_c : c ≤ ε * Real.sqrt (Real.log N) := by
    rwa [div_le_iff hε] at h_sqrt_lb
  -- c * √(log N) ≤ ε * log N
  have h_key : c * Real.sqrt (Real.log N) ≤ ε * Real.log N := by
    calc c * Real.sqrt (Real.log N)
        ≤ (ε * Real.sqrt (Real.log N)) * Real.sqrt (Real.log N) :=
          mul_le_mul_of_nonneg_right h_eps_c (Real.sqrt_nonneg _)
      _ = ε * Real.log N := by
          rw [mul_assoc, Real.mul_self_sqrt h_logN_pos.le]
  -- -ε * log N ≤ -c * √(log N) → exp(-ε log N) ≤ exp(-c√log N)
  have h_exp : Real.exp (-ε * Real.log N) ≤ Real.exp (-c * Real.sqrt (Real.log N)) :=
    Real.exp_le_exp.mpr (by linarith)
  -- N^(-ε) = exp(-ε * log N) for N > 0
  have h_rpow : (N : ℝ) ^ (-ε) = Real.exp (-ε * Real.log N) := by
    rw [Real.rpow_def_of_pos hNpos]
    congr 1; ring
  linarith [h_exp, h_rpow.le]

end RothTheoremQuantitativeAristotle
