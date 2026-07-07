/-
  Lp Riesz (σ-finite): Step A1 norm bound `gseq_norm_bound` (converse-Hölder ‖g‖_q ≤ ‖φ‖ on a spanning set).

  Split out of the monolithic `CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01.lean` (S20, researcher-15).
  Rationale: with the S18 drift fixes applied, the combined 1020-line file
  elaborates past the 32GB/40min Docker build envelope, so its error summary
  never flushes. Splitting each ≥300-line theorem into its own file makes each
  piece elaborate independently and within budget, and makes any residual
  Mathlib-drift errors measurable per-file. Same namespace / same public names,
  so downstream imports are unaffected.
-/
import Mathlib
import Proofs.CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01Infra

noncomputable section

open MeasureTheory ENNReal NNReal Set Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszSigmaFiniteComplete

-- ============================================================================
-- § 5. Localization step (Step A — proved)
-- ============================================================================

/-- **Step A1 of `localization_existence`, extracted.** For a single spanning set
`Sₙ`, the finite-measure Riesz representer `g` on `μ.restrict Sₙ` satisfies the
converse-Hölder norm bound `‖g‖_{Lq(μ|Sₙ)} ≤ ‖φ‖`.  Split out of the monolithic
`localization_existence` (S18: the 600-line theorem exceeded the 40min/32GB build
envelope once further drift fixes let elaboration proceed) so each piece
elaborates independently and within budget. -/
theorem gseq_norm_bound
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ] [Fact (1 ≤ p)]
    (φ : Lp ℝ p μ →L[ℝ] ℝ) (n : ℕ) (hp0 : p ≠ 0)
    (g : α → ℝ)
    (hg : MemLp g q (μ.restrict (spanningSets μ n)))
    (hgrep : ∀ f : Lp ℝ p (μ.restrict (spanningSets μ n)),
        φ (extByZeroCLM (measurableSet_spanningSets μ n) hp0 hptop f) =
        ∫ a, (f : α → ℝ) a * g a ∂(μ.restrict (spanningSets μ n))) :
    eLpNorm g q (μ.restrict (spanningSets μ n)) ≤ ENNReal.ofReal ‖φ‖ := by
    set μₙ := μ.restrict (spanningSets μ n)
    set hS := measurableSet_spanningSets μ n
    set extZ := extByZeroCLM hS hp0 hptop
    -- Derived constants
    have hqtop' : q ≠ ⊤ := by
      intro h; rw [h, ENNReal.toReal_top] at hpq; linarith [hpq.symm.pos]
    have hq0' : q ≠ 0 := by
      intro h; rw [h, ENNReal.toReal_zero] at hpq; linarith [hpq.symm.pos]
    have hq_pos' : 0 < q.toReal := ENNReal.toReal_pos hq0' hqtop'
    have hp_pos' : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
    -- μₙ is finite
    haveI hfin' : IsFiniteMeasure μₙ :=
      { measure_univ_lt_top := by
          simp only [μₙ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
          exact measure_spanningSets_lt_top μ n }
    -- ‖extZ f‖ = ‖f‖ (isometry), hence ‖extZ‖ ≤ 1
    have hextZ_le : ∀ f : Lp ℝ p μₙ, ‖extZ f‖ ≤ ‖f‖ := fun f => by
      simp only [extZ, extByZeroCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
        AddHom.coe_mk, Lp.norm_def]
      have hh := memLp_indicator_of_restrict_loc hS hp0 hptop (Lp.memLp f)
      conv_lhs => rw [eLpNorm_congr_ae hh.coeFn_toLp]
      rw [eLpNorm_indicator_eq_restrict_loc hS _ hp0 hptop]
    have hextZ_norm : ‖extZ‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
        rw [one_mul]; exact hextZ_le f)
    have hphin_le : ‖φ.comp extZ‖ ≤ ‖φ‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) hextZ_norm)
    -- hrep: (φ ∘ extZ) f = ∫ f * g ∂μₙ for all f ∈ Lp(μₙ)
    have hrep : ∀ f : Lp ℝ p μₙ, (φ.comp extZ) f = ∫ a, (f : α → ℝ) a * g a ∂μₙ := by
      intro f; simp only [ContinuousLinearMap.comp_apply]; exact hgrep f
    -- For each truncation g_k := clamp(g, -k, k), prove ‖g_k‖_q ≤ ‖φ ∘ extZ‖
    have htrunc : ∀ k : ℕ,
        eLpNorm (fun a => max (min (g a) (k : ℝ)) (-(k : ℝ))) q μₙ ≤
        ENNReal.ofReal ‖φ.comp extZ‖ := by
      intro k
      set g_k := fun a => max (min (g a) (k : ℝ)) (-(k : ℝ))
      set h_k := fun a => Real.sign (g_k a) * |g_k a| ^ (q.toReal - 1)
      -- |g_k a| ≤ k
      have hgk_bound : ∀ a, |g_k a| ≤ (k : ℝ) := fun a => by
        simp only [g_k, abs_le]
        constructor
        · linarith [le_max_right (min (g a) (k : ℝ)) (-(k : ℝ))]
        · exact max_le_iff.mpr ⟨min_le_right _ _, neg_le_self (Nat.cast_nonneg k)⟩
      -- g_k is AEStronglyMeasurable and integrable on μₙ
      have hgk_asm : AEStronglyMeasurable g_k μₙ :=
        (hg.1.inf measurable_const.aestronglyMeasurable).sup
          measurable_const.aestronglyMeasurable
      have hgk_int : Integrable g_k μₙ := by
        rw [← memLp_one_iff_integrable]
        exact MemLp.of_bound hgk_asm (k : ℝ)
          (ae_of_all μₙ fun a => by
            simp only [Real.norm_eq_abs]; exact hgk_bound a)
      -- h_k is bounded and in Lp
      have hhk_bound : ∀ᵐ a ∂μₙ, ‖h_k a‖ ≤ (k : ℝ) ^ (q.toReal - 1) :=
        ae_of_all μₙ fun a => by
          simp only [h_k, Real.norm_eq_abs, abs_mul]
          rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (g_k a)) (q.toReal - 1))]
          calc |Real.sign (g_k a)| * |g_k a| ^ (q.toReal - 1)
              ≤ 1 * |g_k a| ^ (q.toReal - 1) :=
                  mul_le_mul_of_nonneg_right
                    (by rcases Real.sign_apply_eq (g_k a) with h | h | h <;>
                        rw [h] <;> norm_num) (by positivity)
            _ = |g_k a| ^ (q.toReal - 1) := one_mul _
            _ ≤ (k : ℝ) ^ (q.toReal - 1) :=
                  Real.rpow_le_rpow (abs_nonneg _) (hgk_bound a)
                    (by linarith [hpq.symm.lt])
      have hhk_meas : AEStronglyMeasurable h_k μₙ := by
        apply AEStronglyMeasurable.mul
        · exact (measurable_real_sign.comp_aemeasurable
              hgk_asm.aemeasurable).aestronglyMeasurable
        · have hrpow : Continuous (fun x : ℝ => x ^ (q.toReal - 1)) :=
            continuous_id.rpow_const fun _ => Or.inr (by linarith [hpq.symm.lt])
          exact hrpow.comp_aestronglyMeasurable hgk_asm.norm
      have hhk_memLp : MemLp h_k p μₙ :=
        MemLp.of_bound hhk_meas ((k : ℝ) ^ (q.toReal - 1)) hhk_bound
      -- φₙ(h_k) = ∫ h_k * g ∂μₙ (direct from hrep)
      have hphi_hk : (φ.comp extZ) (hhk_memLp.toLp h_k) = ∫ a, h_k a * g a ∂μₙ := by
        rw [hrep (hhk_memLp.toLp h_k)]
        apply integral_congr_ae
        filter_upwards [hhk_memLp.coeFn_toLp] with a ha; rw [ha]
      -- Pointwise: h_k(a) * g_k(a) ≤ h_k(a) * g(a)  (sign agreement)
      have hpw : ∀ a, h_k a * g_k a ≤ h_k a * g a := fun a => by
        suffices 0 ≤ h_k a * (g a - g_k a) by linarith [mul_sub (h_k a) (g a) (g_k a)]
        simp only [h_k, g_k]
        rcases le_or_gt (g a) (-(k : ℝ)) with h1 | h1
        · have : max (min (g a) ↑k) (-(↑k : ℝ)) = -(↑k : ℝ) :=
              max_eq_right (le_trans (min_le_left _ _) h1)
          rw [this]
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp
          · rw [Real.sign_of_neg (neg_lt_zero.mpr (Nat.cast_pos.mpr hk))]
            have h2 : (-1 : ℝ) * |(-(k : ℝ))| ^ (q.toReal - 1) ≤ 0 := by
              rw [neg_one_mul, neg_nonpos]
              exact Real.rpow_nonneg (abs_nonneg _) _
            have h3 : g a - -(k : ℝ) ≤ 0 := by linarith
            have h4 := mul_nonneg (neg_nonneg.mpr h2) (neg_nonneg.mpr h3)
            rwa [neg_mul_neg] at h4
        rcases le_or_gt (k : ℝ) (g a) with h2 | h2
        · have : max (min (g a) ↑k) (-(↑k : ℝ)) = (↑k : ℝ) :=
              by rw [min_eq_right h2, max_eq_left (neg_le_self (Nat.cast_nonneg k))]
          rw [this]
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp
          · rw [Real.sign_of_pos (Nat.cast_pos.mpr hk)]
            exact mul_nonneg (mul_nonneg zero_le_one
              (Real.rpow_nonneg (abs_nonneg _) _)) (by linarith)
        · have : max (min (g a) ↑k) (-(↑k : ℝ)) = g a :=
              by rw [min_eq_left h2.le, max_eq_left (le_of_lt h1)]
          rw [this, sub_self, mul_zero]
      -- ∫ h_k * g_k = ‖g_k‖_q^q  (algebraic identity)
      have hgk_memLq : MemLp g_k q μₙ := by
        refine ⟨hgk_asm, ?_⟩
        calc eLpNorm g_k q μₙ
            ≤ eLpNorm (fun _ => (k : ℝ)) q μₙ := by
                apply eLpNorm_mono_ae
                exact ae_of_all μₙ fun a => by
                  simp [Real.norm_eq_abs]; exact hgk_bound a
          _ < ⊤ := (memLp_const (k : ℝ)).eLpNorm_lt_top
      have hrpow_id : ∀ x : ℝ, 0 ≤ x → x ^ (q.toReal - 1) * x = x ^ q.toReal := by
        intro x hx
        rcases hx.eq_or_lt with hx0 | hx'
        · rw [← hx0, mul_zero, Real.zero_rpow hq_pos'.ne']
        · nth_rewrite 2 [← Real.rpow_one x]
          rw [← Real.rpow_add hx', show q.toReal - 1 + 1 = q.toReal from by ring]
      have hint_hkgk : ∫ a, h_k a * g_k a ∂μₙ = (eLpNorm g_k q μₙ ^ q.toReal).toReal := by
        have hpw2 : ∀ a, h_k a * g_k a = |g_k a| ^ q.toReal := fun a => by
          simp only [h_k]
          have hsign : Real.sign (g_k a) * g_k a = |g_k a| := by
            rcases lt_trichotomy (g_k a) 0 with ha | ha | ha
            · simp [Real.sign_of_neg ha, abs_of_neg ha]
            · simp [ha]
            · simp [Real.sign_of_pos ha, abs_of_pos ha]
          rw [show Real.sign (g_k a) * |g_k a| ^ (q.toReal - 1) * g_k a =
              |g_k a| ^ (q.toReal - 1) * (Real.sign (g_k a) * g_k a) from by ring,
              hsign, hrpow_id _ (abs_nonneg _)]
        simp_rw [hpw2]
        have hpw3 : ∀ a, |g_k a| ^ q.toReal =
            (‖g_k a‖ₑ ^ q.toReal).toReal := fun a => by
          rw [enorm_eq_nnnorm, ← ENNReal.coe_rpow_of_nonneg _ (le_of_lt hq_pos'),
              ENNReal.coe_toReal, NNReal.coe_rpow]
          simp [Real.norm_eq_abs]
        simp_rw [hpw3]
        have hf_lt_top : ∀ᵐ a ∂μₙ, ‖g_k a‖ₑ ^ q.toReal < ⊤ :=
          ae_of_all μₙ fun a => by
            rw [enorm_eq_nnnorm, ← ENNReal.coe_rpow_of_nonneg _ (le_of_lt hq_pos')]
            exact ENNReal.coe_lt_top
        rw [integral_toReal (hgk_asm.enorm.pow_const q.toReal) hf_lt_top]
        congr 1
        rw [eLpNorm_eq_lintegral_rpow_enorm hq0' hqtop', ← ENNReal.rpow_mul,
            one_div, inv_mul_cancel₀ hq_pos'.ne', ENNReal.rpow_one]
      -- ‖h_k‖_p = ‖g_k‖_q^(q/p)  (norm identity via hpq)
      have hpq_prod : p.toReal * q.toReal = p.toReal + q.toReal := by
        have h := hpq.inv_add_inv_eq_one
        field_simp [hp_pos'.ne', hq_pos'.ne'] at h; linarith
      have hn_eLpNorm : eLpNorm h_k p μₙ = eLpNorm g_k q μₙ ^ (q.toReal / p.toReal) := by
        have hpw_real : ∀ a, |h_k a| ^ p.toReal = |g_k a| ^ q.toReal := fun a => by
          simp only [h_k]
          rcases eq_or_ne (g_k a) 0 with ha | ha
          · simp [ha, Real.sign_zero, Real.zero_rpow hp_pos'.ne', Real.zero_rpow hq_pos'.ne']
          · have habs_pos : 0 < |g_k a| := abs_pos.mpr ha
            have hsign1 : |Real.sign (g_k a)| = 1 := by
              rcases lt_trichotomy (g_k a) 0 with h | h | h
              · simp [Real.sign_of_neg h]
              · exact absurd h ha
              · simp [Real.sign_of_pos h]
            rw [abs_mul, hsign1, one_mul,
                abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
                ← Real.rpow_mul (abs_nonneg _)]
            congr 1; nlinarith [hpq_prod]
        have hpw_enn : ∀ a, ‖h_k a‖ₑ ^ p.toReal = ‖g_k a‖ₑ ^ q.toReal := fun a => by
          simp only [enorm_eq_nnnorm]
          rw [← ENNReal.coe_rpow_of_nonneg _ (le_of_lt hp_pos'),
              ← ENNReal.coe_rpow_of_nonneg _ (le_of_lt hq_pos')]
          norm_cast; apply NNReal.coe_injective
          simp only [NNReal.coe_rpow, coe_nnnorm, Real.norm_eq_abs]
          exact hpw_real a
        rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hptop,
            eLpNorm_eq_lintegral_rpow_enorm hq0' hqtop',
            lintegral_congr (fun a => hpw_enn a), ← ENNReal.rpow_mul]
        congr 1; field_simp [hp_pos'.ne', hq_pos'.ne']
      -- Assemble: ‖g_k‖_q^q ≤ ‖φ ∘ extZ‖ * ‖g_k‖_q^(q/p) → ‖g_k‖_q ≤ ‖φ ∘ extZ‖
      set x := (eLpNorm g_k q μₙ).toReal
      have hx_nn : 0 ≤ x := ENNReal.toReal_nonneg
      have hgk_ne_top : eLpNorm g_k q μₙ ≠ ⊤ := hgk_memLq.eLpNorm_lt_top.ne
      have hqp_eq : q.toReal / p.toReal + 1 = q.toReal := by
        field_simp [hp_pos'.ne']; linarith [hpq_prod]
      have hint_hkg_int : Integrable (fun a => h_k a * g_k a) μₙ :=
        integrable_mul_sf p q hpq (le_of_lt hp1) hptop hhk_memLp hgk_memLq
      have hint_hg_int : Integrable (fun a => h_k a * g a) μₙ :=
        integrable_mul_sf p q hpq (le_of_lt hp1) hptop hhk_memLp hg
      have hint_ineq : ∫ a, h_k a * g_k a ∂μₙ ≤ ∫ a, h_k a * g a ∂μₙ :=
        integral_mono hint_hkg_int hint_hg_int (fun a => hpw a)
      have hn_norm : ‖hhk_memLp.toLp h_k‖ = (eLpNorm h_k p μₙ).toReal := by
        simp only [Lp.norm_def]
        congr 1; exact eLpNorm_congr_ae hhk_memLp.coeFn_toLp
      have hchain : x ^ q.toReal ≤ ‖φ.comp extZ‖ * x ^ (q.toReal / p.toReal) := by
        have hlhs : x ^ q.toReal = (eLpNorm g_k q μₙ ^ q.toReal).toReal := by
          simp [x, ENNReal.toReal_rpow]
        have hrhs_eq : x ^ (q.toReal / p.toReal) = (eLpNorm h_k p μₙ).toReal := by
          rw [hn_eLpNorm]; simp [x, ENNReal.toReal_rpow]
        rw [hlhs, hrhs_eq]
        calc (eLpNorm g_k q μₙ ^ q.toReal).toReal
            = ∫ a, h_k a * g_k a ∂μₙ := hint_hkgk.symm
          _ ≤ ∫ a, h_k a * g a ∂μₙ := hint_ineq
          _ = (φ.comp extZ) (hhk_memLp.toLp h_k) := hphi_hk.symm
          _ ≤ ‖(φ.comp extZ) (hhk_memLp.toLp h_k)‖ := le_abs_self _
          _ ≤ ‖φ.comp extZ‖ * ‖hhk_memLp.toLp h_k‖ :=
                ContinuousLinearMap.le_opNorm _ _
          _ = ‖φ.comp extZ‖ * (eLpNorm h_k p μₙ).toReal := by rw [hn_norm]
      have hx_le : x ≤ ‖φ.comp extZ‖ := by
        rcases le_or_gt x 0 with hx | hx
        · linarith [norm_nonneg (φ.comp extZ)]
        · have hrpow : x ^ q.toReal = x ^ (q.toReal / p.toReal) * x := by
            conv_lhs =>
              rw [show q.toReal = q.toReal / p.toReal + 1 from by linarith [hqp_eq]]
            rw [Real.rpow_add hx, Real.rpow_one]
          have hxqp_pos : 0 < x ^ (q.toReal / p.toReal) := Real.rpow_pos_of_pos hx _
          have : x ^ (q.toReal / p.toReal) * x ≤ x ^ (q.toReal / p.toReal) * ‖φ.comp extZ‖ := by
            calc x ^ (q.toReal / p.toReal) * x
                = x ^ q.toReal := hrpow.symm
              _ ≤ ‖φ.comp extZ‖ * x ^ (q.toReal / p.toReal) := hchain
              _ = x ^ (q.toReal / p.toReal) * ‖φ.comp extZ‖ := mul_comm _ _
          exact le_of_mul_le_mul_left this hxqp_pos
      calc eLpNorm g_k q μₙ
          = ENNReal.ofReal x := (ENNReal.ofReal_toReal hgk_ne_top).symm
        _ ≤ ENNReal.ofReal ‖φ.comp extZ‖ := ENNReal.ofReal_le_ofReal hx_le
    -- MCT: eLpNorm g q μₙ ≤ ENNReal.ofReal ‖φ ∘ extZ‖ ≤ ENNReal.ofReal ‖φ‖
    apply le_trans _ (ENNReal.ofReal_le_ofReal hphin_le)
    rw [eLpNorm_eq_lintegral_rpow_enorm hq0' hqtop']
    -- ∫⁻ ‖g‖^q = ⨆_k ∫⁻ ‖g_k‖^q  (truncation MCT, mirrors rn_deriv_memLq_from_trunc)
    have hgn_lint : ∀ k : ℕ,
        ∫⁻ a, ‖(fun a => max (min (g a) (k : ℝ)) (-(k : ℝ))) a‖ₑ ^ q.toReal ∂μₙ ≤
        (ENNReal.ofReal ‖φ.comp extZ‖) ^ q.toReal := fun k => by
      have h := htrunc k
      rw [eLpNorm_eq_lintegral_rpow_enorm hq0' hqtop'] at h
      calc ∫⁻ a, _ ∂μₙ
          = ((∫⁻ a, _ ∂μₙ) ^ (1 / q.toReal)) ^ q.toReal := by
              rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq_pos'.ne', ENNReal.rpow_one]
        _ ≤ (ENNReal.ofReal ‖φ.comp extZ‖) ^ q.toReal :=
              ENNReal.rpow_le_rpow h (le_of_lt hq_pos')
    have hMCT : ∫⁻ a, ‖g a‖ₑ ^ q.toReal ∂μₙ =
        ⨆ k : ℕ, ∫⁻ a, ‖(fun a => max (min (g a) (k : ℝ)) (-(k : ℝ))) a‖ₑ
          ^ q.toReal ∂μₙ := by
      have abs_clamp : ∀ (r : ℝ) (k : ℕ), |max (min r k) (-(k : ℝ))| = min |r| k := by
        intro r k
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        rcases le_or_gt r (-(k : ℝ)) with h1 | h1
        · rw [min_eq_left (h1.trans (by linarith)), max_eq_right h1,
              abs_neg, abs_of_nonneg hk, abs_of_nonpos (h1.trans (by linarith)),
              min_eq_right (by linarith)]
        rcases le_or_gt (k : ℝ) r with h2 | h2
        · rw [min_eq_right h2, max_eq_left (by linarith), abs_of_nonneg hk,
              abs_of_nonneg (hk.trans h2), min_eq_right h2]
        · rw [min_eq_left h2.le, max_eq_left h1.le,
              min_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)]
      have norm_gk_eq : ∀ (a : α) (k : ℕ),
          ‖max (min (g a) (k : ℝ)) (-(k : ℝ))‖ₑ = min ‖g a‖ₑ (k : ℝ≥0∞) := by
        intro a k
        have h : ‖max (min (g a) (k : ℝ)) (-(k : ℝ))‖₊ = min ‖g a‖₊ (k : ℝ≥0) := by
          apply NNReal.coe_injective
          push_cast [Real.norm_eq_abs]
          exact abs_clamp (g a) k
        simp only [enorm_eq_nnnorm]
        rw [h, ENNReal.coe_min]
        norm_cast
      have ptwise_eq : ∀ a, ‖g a‖ₑ ^ q.toReal =
          ⨆ k : ℕ, (min ‖g a‖ₑ (k : ℝ≥0∞)) ^ q.toReal := fun a => by
        obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt (enorm_ne_top (x := g a))
        apply le_antisymm
        · exact le_iSup_of_le K (le_of_eq (by rw [min_eq_left hK.le]))
        · exact iSup_le fun k =>
            ENNReal.rpow_le_rpow (min_le_left _ _) (le_of_lt hq_pos')
      rw [show (fun a => ‖g a‖ₑ ^ q.toReal) =
          (fun a => ⨆ k : ℕ, (min ‖g a‖ₑ (k : ℝ≥0∞)) ^ q.toReal) from funext ptwise_eq,
          lintegral_iSup'
            (fun k => (hg.1.enorm.min aemeasurable_const).pow_const q.toReal)
            (ae_of_all μₙ fun a m k hmk => ENNReal.rpow_le_rpow
              (min_le_min_left _ (Nat.cast_le.mpr hmk)) (le_of_lt hq_pos'))]
      simp_rw [← norm_gk_eq]
    calc (∫⁻ a, ‖g a‖ₑ ^ q.toReal ∂μₙ) ^ (1 / q.toReal)
        ≤ ((ENNReal.ofReal ‖φ.comp extZ‖) ^ q.toReal) ^ (1 / q.toReal) := by
            apply ENNReal.rpow_le_rpow _ (by positivity)
            rw [hMCT]; exact iSup_le hgn_lint
      _ = ENNReal.ofReal ‖φ.comp extZ‖ := by
            rw [← ENNReal.rpow_mul, mul_one_div_cancel hq_pos'.ne', ENNReal.rpow_one]

end RieszSigmaFiniteComplete

end
