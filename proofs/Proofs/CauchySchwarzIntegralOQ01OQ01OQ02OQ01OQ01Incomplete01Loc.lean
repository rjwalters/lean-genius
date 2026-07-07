/-
  Lp Riesz (σ-finite): Step A `localization_existence` (glue per-spanning-set representers into a global g ∈ Lq(μ)).

  Split out of the monolithic `CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01.lean` (S20, researcher-15).
  Rationale: with the S18 drift fixes applied, the combined 1020-line file
  elaborates past the 32GB/40min Docker build envelope, so its error summary
  never flushes. Splitting each ≥300-line theorem into its own file makes each
  piece elaborate independently and within budget, and makes any residual
  Mathlib-drift errors measurable per-file. Same namespace / same public names,
  so downstream imports are unaffected.
-/
import Mathlib
import Proofs.CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01Norm

noncomputable section

open MeasureTheory ENNReal NNReal Set Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszSigmaFiniteComplete

/-- **Step A**: constructs g ∈ Lq(μ) with indicator agreement on finite-measure sets.

    Proof outline (Folland §6.2):
    1. For each n, μ.restrict(Sₙ) is finite. Build φₙ = φ ∘ extByZeroCLM.
    2. Apply `RieszLpSurjectivity.riesz_lp_surjective_from_rn` to get gₙ ∈ Lq(μₙ).
    3. Consistency: gₙ₊₁ = gₙ a.e. on Sₙ (Lq uniqueness).
    4. MCT + uniform bound ‖gₙ‖_{Lq(μₙ)} ≤ ‖φₙ‖ ≤ ‖φ‖ gives g ∈ Lq(μ).
    5. Indicator agreement via continuity of φ and DCT.
    Infrastructure (extByZeroCLM, finite-measure application) is proved above.
    All steps proved below; 0 sorries. -/
theorem localization_existence
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ] [Fact (1 ≤ p)]
    (φ : Lp ℝ p μ →L[ℝ] ℝ) :
    ∃ g : α → ℝ, MemLp g q μ ∧
      eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖ ∧
      ∀ (E : Set α) (hE : MeasurableSet E) (hfin : μ E ≠ ⊤),
        φ ((memLp_indicator_const p hE 1 (Or.inr hfin)).toLp _) =
        ∫ a in E, g a ∂μ := by
  classical
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_of_lt hp1))
  -- For each n, finite-measure Riesz on μ.restrict(Sₙ) via φₙ = φ ∘ extByZeroCLM
  have hriesz_n : ∀ n, ∃ gₙ : α → ℝ,
      MemLp gₙ q (μ.restrict (spanningSets μ n)) ∧
      ∀ f : Lp ℝ p (μ.restrict (spanningSets μ n)),
        φ (extByZeroCLM (measurableSet_spanningSets μ n) hp0 hptop f) =
        ∫ a, (f : α → ℝ) a * gₙ a ∂(μ.restrict (spanningSets μ n)) := by
    intro n
    haveI hfin_n : IsFiniteMeasure (μ.restrict (spanningSets μ n)) :=
      { measure_univ_lt_top := by
          have : (μ.restrict (spanningSets μ n)) Set.univ =
              μ (spanningSets μ n) := by
            rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
          rw [this]; exact measure_spanningSets_lt_top μ n }
    haveI : SigmaFinite (μ.restrict (spanningSets μ n)) := inferInstance
    let φₙ : Lp ℝ p (μ.restrict (spanningSets μ n)) →L[ℝ] ℝ :=
      φ.comp (extByZeroCLM (measurableSet_spanningSets μ n) hp0 hptop)
    obtain ⟨gₙ, hgₙ, hgₙ_rep⟩ :=
      RieszLpSurjectivity.riesz_lp_surjective_from_rn p q hp1 hptop hpq φₙ
    exact ⟨gₙ, hgₙ, hgₙ_rep⟩
  -- Extract the gₙ family
  choose g_seq hg_seq_mem hg_seq_rep using hriesz_n
  -- Key: extByZeroCLM(Sₙ)(1_E^Lp(μₙ)) = 1_E^Lp(μ), for E ⊆ Sₙ
  -- (Both have representative E.indicator 1 a.e. w.r.t. μ)
  have hext_ind : ∀ n (E : Set α) (hE : MeasurableSet E) (hEn : E ⊆ spanningSets μ n)
      (hfin : μ E ≠ ⊤),
      extByZeroCLM (measurableSet_spanningSets μ n) hp0 hptop
        ((memLp_indicator_const p hE 1 (Or.inr (show (μ.restrict (spanningSets μ n)) E ≠ ⊤ from by
            rw [Measure.restrict_apply hE, Set.inter_eq_left.mpr hEn]; exact hfin))).toLp _) =
      (memLp_indicator_const p hE 1 (Or.inr hfin)).toLp _ := by
    intro n E hE hEn hfin
    have hfin_n : (μ.restrict (spanningSets μ n)) E ≠ ⊤ := by
      rw [Measure.restrict_apply hE, Set.inter_eq_left.mpr hEn]; exact hfin
    rw [Lp.ext_iff]
    -- Show both cofunctions are a.e. E.indicator 1 under μ
    have hlhs : (extByZeroCLM (measurableSet_spanningSets μ n) hp0 hptop
        ((memLp_indicator_const p hE 1 (Or.inr hfin_n)).toLp _) : α → ℝ) =ᵐ[μ]
        (spanningSets μ n).indicator
          ((memLp_indicator_const p hE 1 (Or.inr hfin_n)).toLp _ : α → ℝ) :=
      (memLp_indicator_of_restrict_loc (measurableSet_spanningSets μ n) hp0 hptop
        (Lp.memLp _)).coeFn_toLp
    have hrhs : ((memLp_indicator_const p hE 1 (Or.inr hfin)).toLp _ : α → ℝ) =ᵐ[μ]
        E.indicator 1 :=
      (memLp_indicator_const p hE 1 (Or.inr hfin)).coeFn_toLp
    -- Sₙ.indicator (coeFn of 1_E^Lp(μₙ)) =ᵐ[μ] E.indicator 1
    -- coeFn_toLp gives =ᵐ[μ.restrict Sₙ]; convert to =ᵐ[μ] via ae_restrict_iff'
    have hkey : (spanningSets μ n).indicator
        ((memLp_indicator_const p hE 1 (Or.inr hfin_n)).toLp _ : α → ℝ) =ᵐ[μ]
        E.indicator 1 := by
      have hcoe_restrict : ∀ᵐ a ∂μ, a ∈ spanningSets μ n →
          ((memLp_indicator_const p hE (1 : ℝ) (Or.inr hfin_n)).toLp _ : α → ℝ) a =
            E.indicator (fun _ => (1 : ℝ)) a :=
        (ae_restrict_iff' (measurableSet_spanningSets μ n)).mp
          (memLp_indicator_const p hE (1 : ℝ) (Or.inr hfin_n)).coeFn_toLp
      filter_upwards [hcoe_restrict] with a ha
      simp only [Set.indicator_apply]
      by_cases hn : a ∈ spanningSets μ n
      · simp only [hn, ite_true]; exact ha hn
      · simp only [hn, ite_false, Set.indicator_apply, if_neg (fun he => hn (hEn he))]
    exact hlhs.trans hkey |>.trans hrhs.symm
  -- For E ⊆ Sₙ with μ(E) < ∞: φ(1_E^Lp(μ)) = ∫_E g_seq n dμ
  have hagree_n : ∀ n (E : Set α) (hE : MeasurableSet E) (hEn : E ⊆ spanningSets μ n)
      (hfin : μ E ≠ ⊤),
      φ ((memLp_indicator_const p hE 1 (Or.inr hfin)).toLp _) =
      ∫ a in E, g_seq n a ∂μ := by
    intro n E hE hEn hfin
    have hfin_n : (μ.restrict (spanningSets μ n)) E ≠ ⊤ := by
      rw [Measure.restrict_apply hE, Set.inter_eq_left.mpr hEn]; exact hfin
    -- φ(1_E) = φ(extByZeroCLM(1_E^Lp(μₙ))) = ∫ 1_E * g_seq n ∂μₙ = ∫_E g_seq n ∂μ
    rw [← hext_ind n E hE hEn hfin]
    rw [hg_seq_rep n]
    -- ∫ (coeFn of 1_E^Lp(μₙ)) * g_seq n ∂(μ.restrict Sₙ) = ∫_E g_seq n ∂μ
    have hcoe : ((memLp_indicator_const p hE 1 (Or.inr hfin_n)).toLp _ : α → ℝ) =ᵐ[μ.restrict (spanningSets μ n)]
        E.indicator 1 :=
      (memLp_indicator_const p hE 1 (Or.inr hfin_n)).coeFn_toLp
    have hstep : (fun a => ((memLp_indicator_const p hE 1 (Or.inr hfin_n)).toLp _ : α → ℝ) a
          * g_seq n a) =ᵐ[μ.restrict (spanningSets μ n)]
        fun a => E.indicator (g_seq n) a := by
      filter_upwards [hcoe] with a ha
      rw [ha]
      simp only [Set.indicator_apply, Pi.one_apply, ite_mul, one_mul, zero_mul]
    rw [integral_congr_ae hstep]
    rw [integral_indicator hE, Measure.restrict_restrict hE,
      Set.inter_eq_left.mpr hEn]
  -- ── Step A1: Norm bound ─────────────────────────────────────────────────────
  -- Hölder-extremizer norm bound: ‖g_seq n‖_{Lq(μ.restrict Sₙ)} ≤ ‖φ‖
  -- Proof sketch: let φₙ := φ ∘ extByZeroCLM(Sₙ); then ‖φₙ‖ ≤ ‖φ‖.
  -- riesz_lp_surjective_from_rn gives g_seq n with ‖g_seq n‖_Lq = ‖φₙ‖ ≤ ‖φ‖.
  -- The equality uses the Hölder extremizer (cf. holder_extremizer_lq_bound in parent).
  have hgnorm : ∀ n, eLpNorm (g_seq n) q (μ.restrict (spanningSets μ n)) ≤
      ENNReal.ofReal ‖φ‖ := fun n =>
    gseq_norm_bound p q hp1 hptop hpq φ n hp0 (g_seq n) (hg_seq_mem n) (hg_seq_rep n)
  -- ── Step A2: Consistency ────────────────────────────────────────────────────
  -- g_seq m =ᵐ[μ.restrict Sₘ] g_seq n for m ≤ n, via set-integral uniqueness.
  -- Key: ∫_s gₘ ∂(μ.restrict Sₘ) = ∫_{s∩Sₘ} gₘ ∂μ = φ(1_{s∩Sₘ}) = ∫_{s∩Sₘ} gₙ ∂μ
  --    = ∫_s gₙ ∂(μ.restrict Sₘ)  [for all measurable s].
  have hconsist : ∀ m n : ℕ, m ≤ n →
      g_seq m =ᵐ[μ.restrict (spanningSets μ m)] g_seq n := by
    intro m n hmn
    haveI hfin_m : IsFiniteMeasure (μ.restrict (spanningSets μ m)) :=
      { measure_univ_lt_top := by
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
          exact measure_spanningSets_lt_top μ m }
    -- Integrability on (μ.restrict Sm) for both sides:
    -- 1 ≤ q from hpq.symm.lt : 1 < q.toReal (lift ℝ inequality to ℝ≥0∞)
    have hq_ge1 : (1 : ℝ≥0∞) ≤ q := by
      have h1 : (1 : ℝ) < q.toReal := hpq.symm.lt
      have hqtop : q ≠ ⊤ := by
        rintro rfl; rw [ENNReal.toReal_top] at h1; linarith
      calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
        _ ≤ ENNReal.ofReal q.toReal := ENNReal.ofReal_le_ofReal h1.le
        _ = q := ENNReal.ofReal_toReal hqtop
    have hgm_int : Integrable (g_seq m) (μ.restrict (spanningSets μ m)) :=
      (hg_seq_mem m).integrable hq_ge1
    have hgn_small : MemLp (g_seq n) q (μ.restrict (spanningSets μ m)) :=
      (hg_seq_mem n).mono_measure (Measure.restrict_mono (monotone_spanningSets μ hmn) le_rfl)
    have hgn_int : Integrable (g_seq n) (μ.restrict (spanningSets μ m)) :=
      hgn_small.integrable hq_ge1
    apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
        (fun s _ _ => hgm_int.integrableOn)
        (fun s _ _ => hgn_int.integrableOn)
    intro s hs _
    -- ∫_s f ∂(μ.restrict Sm) = ∫_{s ∩ Sm} f ∂μ  (Measure.restrict_restrict)
    have to_mu : ∀ f : α → ℝ,
        ∫ a in s, f a ∂(μ.restrict (spanningSets μ m)) =
        ∫ a in s ∩ spanningSets μ m, f a ∂μ := fun f => by
      rw [show (μ.restrict (spanningSets μ m)).restrict s = μ.restrict (s ∩ spanningSets μ m)
            from Measure.restrict_restrict' (measurableSet_spanningSets μ m)]
    simp_rw [to_mu]
    have hfin_int : μ (s ∩ spanningSets μ m) ≠ ⊤ :=
      ((measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top μ m)).ne
    have hEn_m : s ∩ spanningSets μ m ⊆ spanningSets μ m := Set.inter_subset_right
    have hEn_n : s ∩ spanningSets μ m ⊆ spanningSets μ n :=
      hEn_m.trans (monotone_spanningSets μ hmn)
    exact (hagree_n m _ (hs.inter (measurableSet_spanningSets μ m)) hEn_m hfin_int).symm.trans
          (hagree_n n _ (hs.inter (measurableSet_spanningSets μ m)) hEn_n hfin_int)
  -- ── Step A3: Construct global g ─────────────────────────────────────────────
  -- g(a) := g_seq n₀(a) a, where n₀(a) = first n with a ∈ Sₙ.
  -- By hconsist this is a.e. equal to g_seq n on every Sₙ.
  have hcover : ∀ a : α, ∃ n, a ∈ spanningSets μ n := fun a => by
    have := (iUnion_spanningSets μ).symm ▸ mem_univ a
    exact mem_iUnion.mp this
  let idx : α → ℕ := fun a => Nat.find (hcover a)
  let g : α → ℝ := fun a => g_seq (idx a) a
  -- ── Step A4: MemLp g q μ (via MCT + hgnorm) ─────────────────────────────────
  -- eLpNorm(g, q, μ)^q = ∫⁻ |g|^q dμ = ⨆_n ∫⁻_{Sₙ} |g|^q dμ [MCT, Sₙ ↑ univ]
  --                     = ⨆_n ∫⁻_{Sₙ} |g_seq n|^q dμ       [g = g_seq n a.e. on Sₙ]
  --                     ≤ ⨆_n ‖φ‖^q = ‖φ‖^q                 [by hgnorm]
  -- AEStronglyMeasurable g: each g_seq n is AEStronglyMeasurable on μ.restrict Sₙ;
  -- since Sₙ ↑ univ, g is AEStronglyMeasurable on μ.
  -- Derived constants needed below
  have hqtop : q ≠ ⊤ := by
    intro h; rw [h, ENNReal.toReal_top] at hpq; linarith [hpq.symm.pos]
  have hq0 : q ≠ 0 := by
    intro h; rw [h, ENNReal.toReal_zero] at hpq; linarith [hpq.symm.pos]
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  -- g =ᵐ[μ.restrict Sₙ] g_seq n for each n. Hoisted to the theorem's top level: it is
  -- used both in the MemLp/norm proof below AND in the indicator-agreement step at the
  -- end of the theorem (Step A5). For each k ≤ n, hconsist gives a null set on Sₖ where
  -- g_seq k ≠ g_seq n; the finite biUnion over k = 0..n is null and covers the bad set.
  have hg_eq_n : ∀ n, g =ᵐ[μ.restrict (spanningSets μ n)] g_seq n := by
    intro n
    show ∀ᵐ a ∂(μ.restrict (spanningSets μ n)), g a = g_seq n a
    rw [ae_restrict_iff' (measurableSet_spanningSets μ n), ae_iff]
    simp only [_root_.not_imp]
    have hBk_null : ∀ k ≤ n, μ {a | a ∈ spanningSets μ k ∧ g_seq k a ≠ g_seq n a} = 0 :=
      fun k hkn => by
        have h := ae_iff.mp
          ((ae_restrict_iff' (measurableSet_spanningSets μ k)).mp (hconsist k n hkn))
        have hset : {a | a ∈ spanningSets μ k ∧ g_seq k a ≠ g_seq n a} =
            {a | ¬(a ∈ spanningSets μ k → g_seq k a = g_seq n a)} := by
          ext a; simp [_root_.not_imp]
        rw [hset]; exact h
    have h_biUnion_null : μ (⋃ k ∈ Finset.range (n + 1),
        {a | a ∈ spanningSets μ k ∧ g_seq k a ≠ g_seq n a}) = 0 :=
      le_antisymm
        (calc μ (⋃ k ∈ Finset.range (n + 1),
                {a | a ∈ spanningSets μ k ∧ g_seq k a ≠ g_seq n a})
            ≤ ∑ k ∈ Finset.range (n + 1),
                μ {a | a ∈ spanningSets μ k ∧ g_seq k a ≠ g_seq n a} :=
              measure_biUnion_finset_le _ _
          _ = 0 := Finset.sum_eq_zero fun k hk =>
                hBk_null k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
        (zero_le _)
    refine measure_mono_null (fun a ha => ?_) h_biUnion_null
    have hmem : idx a ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.find_min' (hcover a) ha.1))
    exact Set.mem_biUnion hmem ⟨Nat.find_spec (hcover a), ha.2⟩
  -- We prove `MemLp g q μ` together with the converse-Hölder dual-norm bound
  -- `eLpNorm g q μ ≤ ‖φ‖`. The bound is exactly `hg_norm` (Step 3 below); it is the
  -- quantitative content that the maximality reduction in the parent synthesis file
  -- needs to know the supremum `⨆_S ‖g_S‖_q` is finite. Earlier it was computed here
  -- only to discharge `MemLp` and then discarded; we now surface it in the return.
  have hg_lq_norm : MemLp g q μ ∧ eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖ := by
    -- Step 2: AEStronglyMeasurable g μ (hg_eq_n hoisted to theorem top level)
    have hg_asm : AEStronglyMeasurable g μ :=
      aestronglyMeasurable_of_restrict_spanningSets μ fun n =>
        ((hg_seq_mem n).1).congr (hg_eq_n n).symm
    -- Step 3: eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖
    have hg_norm : eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop]
      -- MCT: ∫⁻ ‖g‖^q dμ = ⨆_n ∫⁻_{Sₙ} ‖g‖^q dμ ≤ ⨆_n ‖φ‖^q = ‖φ‖^q
      have hbound_n : ∀ n,
          ∫⁻ a in spanningSets μ n, ‖g a‖ₑ ^ q.toReal ∂μ ≤
          (ENNReal.ofReal ‖φ‖) ^ q.toReal := fun n => by
        have heq : ∫⁻ a in spanningSets μ n, ‖g a‖ₑ ^ q.toReal ∂μ =
            ∫⁻ a, ‖g_seq n a‖ₑ ^ q.toReal ∂(μ.restrict (spanningSets μ n)) := by
          apply lintegral_congr_ae
          filter_upwards [hg_eq_n n] with a ha
          simp [ha]
        rw [heq]
        have h := hgnorm n
        rw [eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop] at h
        have h2 := ENNReal.rpow_le_rpow h (le_of_lt hq_pos)
        rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq_pos.ne', ENNReal.rpow_one] at h2
      -- lintegral over μ = ⨆_n lintegral over μ.restrict Sₙ (Beppo-Levi on spanning sets)
      have hMCT_global : ∫⁻ a, ‖g a‖ₑ ^ q.toReal ∂μ =
          ⨆ n, ∫⁻ a in spanningSets μ n, ‖g a‖ₑ ^ q.toReal ∂μ := by
        set f_ind : ℕ → α → ℝ≥0∞ := fun n a =>
            (spanningSets μ n).indicator (fun _ => ‖g a‖ₑ ^ q.toReal) a
        have hmeas_fn : ∀ n, AEMeasurable (f_ind n) μ := fun n =>
          ((hg_asm.enorm.pow_const q.toReal).indicator
            (measurableSet_spanningSets μ n))
        have hmono : ∀ᵐ a ∂μ, Monotone (fun n => f_ind n a) :=
          ae_of_all μ fun a m n hmn => by
            simp only [f_ind, Set.indicator_apply]
            by_cases hm : a ∈ spanningSets μ m
            · rw [if_pos hm, if_pos (monotone_spanningSets μ hmn hm)]
            · rw [if_neg hm]; exact zero_le _
        have hptwise : ∀ a, ⨆ n, f_ind n a = ‖g a‖ₑ ^ q.toReal := fun a => by
          apply le_antisymm (iSup_le fun n => Set.indicator_le_self _ _ a)
          obtain ⟨n, hn⟩ := Set.mem_iUnion.mp
            ((iUnion_spanningSets μ).symm ▸ Set.mem_univ a)
          have hval : f_ind n a = ‖g a‖ₑ ^ q.toReal :=
            Set.indicator_of_mem hn (fun _ => ‖g a‖ₑ ^ q.toReal)
          exact le_iSup_of_le n hval.ge
        conv_lhs => rw [show (fun a => ‖g a‖ₑ ^ q.toReal) = fun a => ⨆ n, f_ind n a
              from funext (fun a => (hptwise a).symm)]
        rw [lintegral_iSup' hmeas_fn hmono]
        congr 1; ext n
        exact lintegral_indicator (measurableSet_spanningSets μ n) _
      have hle : ∫⁻ a, ‖g a‖ₑ ^ q.toReal ∂μ ≤ (ENNReal.ofReal ‖φ‖) ^ q.toReal := by
        rw [hMCT_global]; exact iSup_le hbound_n
      calc (∫⁻ a, ‖g a‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal)
          ≤ ((ENNReal.ofReal ‖φ‖) ^ q.toReal) ^ (1 / q.toReal) :=
            ENNReal.rpow_le_rpow hle (by positivity)
        _ = ENNReal.ofReal ‖φ‖ := by
            rw [← ENNReal.rpow_mul, mul_one_div_cancel hq_pos.ne', ENNReal.rpow_one]
    exact ⟨⟨hg_asm, lt_of_le_of_lt hg_norm ENNReal.ofReal_lt_top⟩, hg_norm⟩
  obtain ⟨hg_lq, hg_norm⟩ := hg_lq_norm
  -- ── Step A5: Indicator agreement for all E ───────────────────────────────────
  -- For E with μ(E) < ∞:
  --   φ(1_E) = lim_n φ(1_{E∩Sₙ})          [by lp_truncation_tendsto_zero + CLM continuity]
  --          = lim_n ∫_{E∩Sₙ} g dμ         [by hagree_n + g =ᵐ g_seq n on Sₙ]
  --          = ∫_E g dμ                     [by tendsto_setIntegral_of_monotone + DCT]
  refine ⟨g, hg_lq, hg_norm, ?_⟩
  intro E hE hfin
  -- Derived constant: q ≥ 1 (needed for Integrable from MemLp)
  have hq_ge1 : (1 : ℝ≥0∞) ≤ q :=
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal q.toReal :=
          ENNReal.ofReal_le_ofReal hpq.symm.lt.le
      _ = q := ENNReal.ofReal_toReal hqtop
  -- Finite-measure helper for E ∩ Sₙ
  have hfin_n : ∀ n, μ (E ∩ spanningSets μ n) ≠ ⊤ := fun n =>
    ((measure_mono Set.inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfin)).ne
  -- ── Step 1: φ(1_{E∩Sₙ}^Lp) = ∫_{E∩Sₙ} g dμ for each n ──────────────────────
  -- Use hagree_n (E ∩ Sₙ ⊆ Sₙ) to get ∫_{E∩Sₙ} g_seq n, then ae-equality on Sₙ
  have hphi_En : ∀ n,
      φ ((memLp_indicator_const p (hE.inter (measurableSet_spanningSets μ n)) 1
          (Or.inr (hfin_n n))).toLp _) =
      ∫ a in E ∩ spanningSets μ n, g a ∂μ := fun n => by
    rw [hagree_n n (E ∩ spanningSets μ n)
          (hE.inter (measurableSet_spanningSets μ n))
          Set.inter_subset_right (hfin_n n)]
    -- ∫_{E∩Sₙ} g_seq n = ∫_{E∩Sₙ} g  by hg_eq_n restricted to E ∩ Sₙ ⊆ Sₙ
    exact integral_congr_ae ((hg_eq_n n).filter_mono
      (ae_mono (Measure.restrict_mono Set.inter_subset_right le_rfl))).symm
  -- ── Step 2: ∫_{E∩Sₙ} g dμ → ∫_E g dμ  (monotone spanning-set convergence) ────
  have hUnion_E : (⋃ n, E ∩ spanningSets μ n) = E := by
    rw [← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]
  have hg_int_E : Integrable g (μ.restrict (⋃ n, E ∩ spanningSets μ n)) := by
    rw [hUnion_E]
    haveI : IsFiniteMeasure (μ.restrict E) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hfin⟩
    exact (hg_lq.mono_measure Measure.restrict_le_self).integrable hq_ge1
  have htend_int : Tendsto (fun n => ∫ a in E ∩ spanningSets μ n, g a ∂μ)
      atTop (nhds (∫ a in E, g a ∂μ)) := by
    have h := tendsto_setIntegral_of_monotone
      (fun n => hE.inter (measurableSet_spanningSets μ n))
      (fun m n hmn => Set.inter_subset_inter_right E (monotone_spanningSets μ hmn))
      hg_int_E
    rwa [hUnion_E] at h
  -- ── Step 3: φ(1_{E∩Sₙ}^Lp) → φ(1_E^Lp)  (CLM continuity + Lp convergence) ───
  -- φ is bounded: |φ(h_n - h)| ≤ ‖φ‖ * ‖h_n - h‖.
  -- ‖h_n - h‖_Lp = (eLpNorm (1_{E∩Sₙ} - 1_E) p μ).toReal → 0
  -- via lp_truncation_tendsto_zero applied to 1_E (1_{E∩Sₙ} = 1_E * 1_{Sₙ}).
  set hind := indicator_memLp_sf hE hfin p (le_of_lt hp1) hptop
  have htend_phi : Tendsto (fun n =>
      φ ((memLp_indicator_const p (hE.inter (measurableSet_spanningSets μ n)) 1
          (Or.inr (hfin_n n))).toLp _))
      atTop (nhds (φ (hind.toLp _))) := by
    apply (φ.continuous.tendsto _).comp
    -- Need: Tendsto (fun n => h_n n) atTop (nhds (hind.toLp _)) in Lp(μ)
    -- Key: dist (hind.toLp _) (h_n n) = (eLpNorm (1_E - 1_E * 1_{Sₙ}) p μ).toReal → 0
    -- via lp_truncation_tendsto_zero applied to hind = 1_E^MemLp.
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Convert eLpNorm convergence to toReal convergence
    have hlim : Tendsto (fun n => (eLpNorm (fun a => (E.indicator (1 : α → ℝ)) a -
        (E.indicator (1 : α → ℝ)) a * (spanningSets μ n).indicator (1 : α → ℝ) a) p μ).toReal)
        atTop (nhds 0) := by
      have h := (ENNReal.continuousAt_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).tendsto
      have h2 := lp_truncation_tendsto_zero p (le_of_lt hp1) hptop hind
      have h3 := h.comp h2
      simp only [Function.comp, ENNReal.toReal_zero] at h3
      exact h3
    rw [Metric.tendsto_atTop] at hlim
    obtain ⟨N, hN⟩ := hlim ε hε
    refine ⟨N, fun n hn => ?_⟩
    -- Compute dist (h_n n) (hind.toLp _) = (eLpNorm (1_E - 1_E * 1_{Sₙ}) p μ).toReal
    have hdist : dist ((memLp_indicator_const p (hE.inter (measurableSet_spanningSets μ n)) 1
        (Or.inr (hfin_n n))).toLp _) (hind.toLp _) =
        (eLpNorm (fun a => (E.indicator (1 : α → ℝ)) a - (E.indicator (1 : α → ℝ)) a *
            (spanningSets μ n).indicator (1 : α → ℝ) a) p μ).toReal := by
      rw [dist_comm, dist_eq_norm, Lp.norm_def]
      apply congr_arg ENNReal.toReal
      apply eLpNorm_congr_ae
      -- hind.toLp _ - h_n n =ᵐ 1_E - 1_{E∩Sₙ} = 1_E - 1_E * 1_{Sₙ}
      filter_upwards [hind.coeFn_toLp,
        (memLp_indicator_const p (hE.inter (measurableSet_spanningSets μ n)) (1 : ℝ)
          (Or.inr (hfin_n n))).coeFn_toLp,
        Lp.coeFn_sub (hind.toLp _) ((memLp_indicator_const p
          (hE.inter (measurableSet_spanningSets μ n)) 1 (Or.inr (hfin_n n))).toLp _)] with a h1 h2 h3
      rw [h3, Pi.sub_apply, h1, h2]
      -- 1_E a - 1_{E∩Sₙ} a = 1_E a - 1_E a * 1_{Sₙ} a
      simp only [Set.indicator_apply, Set.mem_inter_iff]
      by_cases hEa : a ∈ E <;> by_cases hSa : a ∈ spanningSets μ n <;> simp [hEa, hSa]
    rw [hdist]
    have h := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at h
  -- ── Conclude by tendsto_nhds_unique ──────────────────────────────────────────
  -- Both φ(h_n) → φ(1_E) and φ(h_n) = ∫_{E∩Sₙ} g → ∫_E g, so the limits agree.
  have hseq_eq : (fun n => φ ((memLp_indicator_const p
        (hE.inter (measurableSet_spanningSets μ n)) 1 (Or.inr (hfin_n n))).toLp _)) =
      (fun n => ∫ a in E ∩ spanningSets μ n, g a ∂μ) := funext hphi_En
  exact tendsto_nhds_unique (hseq_eq ▸ htend_phi) htend_int

end RieszSigmaFiniteComplete

end
