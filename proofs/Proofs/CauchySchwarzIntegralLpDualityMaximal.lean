import Mathlib
import Proofs.CauchySchwarzIntegralLpDualityIngredients
import Proofs.CauchySchwarzIntegralLpDualityConsistency
import Proofs.CauchySchwarzIntegralLpDualityGluing
import Proofs.CauchySchwarzIntegralLpDualityExtension

open MeasureTheory ENNReal
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszLpDualityMaximal

/-- **General-measure Riesz reduction (abstract form).**

    Given, for a fixed functional `φ`, an abstract extension-by-zero family `ext`
    with its coeFn characterisation, the σ-finite Riesz theorem *with the norm bound*
    (`Hσ`), and the five already-verified Mathlib-only ingredient facts
    (representer monotonicity `Hmono`, representer consistency `Hcons`, σ-finiteness of a
    countable union `HsigU`, and the gluing/vanishing lemma `Hglue`), the arbitrary-measure
    Riesz representation holds.  This is the Folland (2nd ed.) Theorem 6.16 maximising-hull
    construction: form `c = ⨆_S ‖g_S‖_q ≤ ‖φ‖` over σ-finite-restricted sets, realise it on
    a countable union hull `T`, and for each `f` glue on `U = T ∪ supp f`. -/
theorem riesz_general
    {p q : ℝ≥0∞} (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal) [Fact (1 ≤ p)]
    (φ : Lp ℝ p μ →L[ℝ] ℝ)
    (ext : ∀ (S : Set α), MeasurableSet S → (Lp ℝ p (μ.restrict S) →L[ℝ] Lp ℝ p μ))
    (hext : ∀ (S : Set α) (hS : MeasurableSet S) (f : Lp ℝ p (μ.restrict S)),
      (ext S hS f : α → ℝ) =ᵐ[μ] S.indicator (f : α → ℝ))
    (Hσ : ∀ (S : Set α) (hS : MeasurableSet S), SigmaFinite (μ.restrict S) →
      ∃ g : α → ℝ, MemLp g q (μ.restrict S) ∧
        eLpNorm g q (μ.restrict S) ≤ ENNReal.ofReal ‖φ‖ ∧
        ∀ f : Lp ℝ p (μ.restrict S),
          φ (ext S hS f) = ∫ a, (f : α → ℝ) a * g a ∂(μ.restrict S))
    (Hmono : ∀ {S S' : Set α} (hS : MeasurableSet S) (hS' : MeasurableSet S'), S ⊆ S' →
      ∀ {gS gS' : α → ℝ}, MemLp gS q (μ.restrict S) → MemLp gS' q (μ.restrict S') →
        (∀ f : Lp ℝ p (μ.restrict S), φ (ext S hS f) = ∫ a, (f : α → ℝ) a * gS a ∂(μ.restrict S)) →
        (∀ f : Lp ℝ p (μ.restrict S'), φ (ext S' hS' f) = ∫ a, (f : α → ℝ) a * gS' a ∂(μ.restrict S')) →
        eLpNorm gS q (μ.restrict S) ≤ eLpNorm gS' q (μ.restrict S'))
    (Hcons : ∀ {S S' : Set α} (hS : MeasurableSet S) (hS' : MeasurableSet S'), S ⊆ S' →
      ∀ {gS gS' : α → ℝ}, MemLp gS q (μ.restrict S) → MemLp gS' q (μ.restrict S') →
        (∀ f : Lp ℝ p (μ.restrict S), φ (ext S hS f) = ∫ a, (f : α → ℝ) a * gS a ∂(μ.restrict S)) →
        (∀ f : Lp ℝ p (μ.restrict S'), φ (ext S' hS' f) = ∫ a, (f : α → ℝ) a * gS' a ∂(μ.restrict S')) →
        gS =ᵐ[μ.restrict S] gS')
    (HsigU : ∀ (S : ℕ → Set α), (∀ n, MeasurableSet (S n)) →
      (∀ n, SigmaFinite (μ.restrict (S n))) → SigmaFinite (μ.restrict (⋃ n, S n)))
    (Hglue : ∀ {g : α → ℝ} {T U : Set α}, MeasurableSet T → MeasurableSet U → T ⊆ U →
      q ≠ 0 → q ≠ ∞ → MemLp g q (μ.restrict U) →
      eLpNorm g q (μ.restrict U) ≤ eLpNorm g q (μ.restrict T) →
      g =ᵐ[μ.restrict (U \ T)] 0) :
    ∃ g : α → ℝ, MemLp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1.le).ne'
  have hqtr : (1:ℝ) < q.toReal := (Real.holderConjugate_iff.mp hpq.symm).1
  have hq0 : q ≠ 0 := by rintro rfl; simp only [ENNReal.toReal_zero] at hqtr; linarith
  have hqtop : q ≠ ∞ := by rintro rfl; simp only [ENNReal.toReal_top] at hqtr; linarith
  set A : Set ℝ := {r | ∃ (S : Set α) (hS : MeasurableSet S), SigmaFinite (μ.restrict S) ∧
      ∃ g : α → ℝ, MemLp g q (μ.restrict S) ∧
        eLpNorm g q (μ.restrict S) ≤ ENNReal.ofReal ‖φ‖ ∧
        (∀ f : Lp ℝ p (μ.restrict S), φ (ext S hS f) = ∫ a, (f : α → ℝ) a * g a ∂(μ.restrict S)) ∧
        (eLpNorm g q (μ.restrict S)).toReal = r} with hA_def
  have hAne : A.Nonempty := by
    obtain ⟨g0, hg0, hg0b, hg0r⟩ := Hσ ∅ MeasurableSet.empty (by
      rw [Measure.restrict_empty]; infer_instance)
    exact ⟨_, ∅, MeasurableSet.empty, (by rw [Measure.restrict_empty]; infer_instance),
      g0, hg0, hg0b, hg0r, rfl⟩
  have hAbdd : BddAbove A := by
    refine ⟨‖φ‖, ?_⟩
    rintro r ⟨S, hS, hSσ, g, hg, hgb, hgr, rfl⟩
    have hfin : eLpNorm g q (μ.restrict S) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgb
    calc (eLpNorm g q (μ.restrict S)).toReal
        ≤ (ENNReal.ofReal ‖φ‖).toReal := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hgb
      _ = ‖φ‖ := ENNReal.toReal_ofReal (norm_nonneg _)
  set c : ℝ := sSup A with hc_def
  have hstep : ∀ n : ℕ, ∃ (S : Set α) (hS : MeasurableSet S), SigmaFinite (μ.restrict S) ∧
      ∃ g : α → ℝ, MemLp g q (μ.restrict S) ∧
        eLpNorm g q (μ.restrict S) ≤ ENNReal.ofReal ‖φ‖ ∧
        (∀ f : Lp ℝ p (μ.restrict S), φ (ext S hS f) = ∫ a, (f : α → ℝ) a * g a ∂(μ.restrict S)) ∧
        c - 1 / (n + 1 : ℝ) < (eLpNorm g q (μ.restrict S)).toReal := by
    intro n
    have hlt : c - 1 / (n + 1 : ℝ) < c := by
      have : (0:ℝ) < 1 / (n + 1 : ℝ) := by positivity
      linarith
    obtain ⟨a, haA, hca⟩ := exists_lt_of_lt_csSup hAne hlt
    obtain ⟨S, hS, hSσ, g, hg, hgb, hgr, hgeq⟩ := haA
    exact ⟨S, hS, hSσ, g, hg, hgb, hgr, by rw [hgeq]; exact hca⟩
  choose Sq hSqm hSqσ gq hgqmem hgqb hgqrep hgqapx using hstep
  set T : Set α := ⋃ n, Sq n with hT_def
  have hTm : MeasurableSet T := MeasurableSet.iUnion hSqm
  have hTσ : SigmaFinite (μ.restrict T) := HsigU Sq hSqm hSqσ
  obtain ⟨gT, hgTmem, hgTb, hgTrep⟩ := Hσ T hTm hTσ
  have hgT_fin : eLpNorm gT q (μ.restrict T) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgTb
  have hgT_le_c : (eLpNorm gT q (μ.restrict T)).toReal ≤ c :=
    le_csSup hAbdd ⟨T, hTm, hTσ, gT, hgTmem, hgTb, hgTrep, rfl⟩
  have hc_le_gT : c ≤ (eLpNorm gT q (μ.restrict T)).toReal := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have hsub : Sq n ⊆ T := Set.subset_iUnion Sq n
    have hmono : eLpNorm (gq n) q (μ.restrict (Sq n)) ≤ eLpNorm gT q (μ.restrict T) :=
      Hmono (hSqm n) hTm hsub (hgqmem n) hgTmem (hgqrep n) hgTrep
    have hgqfin : eLpNorm (gq n) q (μ.restrict (Sq n)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hgqb n)
    have hmono' : (eLpNorm (gq n) q (μ.restrict (Sq n))).toReal
        ≤ (eLpNorm gT q (μ.restrict T)).toReal :=
      (ENNReal.toReal_le_toReal hgqfin hgT_fin).mpr hmono
    have hax := hgqapx n
    linarith
  have hNT : (eLpNorm gT q (μ.restrict T)).toReal = c := le_antisymm hgT_le_c hc_le_gT
  refine ⟨T.indicator gT, (memLp_indicator_iff_restrict hTm).mpr hgTmem, ?_⟩
  intro f
  obtain ⟨Sf, hSfm, hf_ae, hSfσ⟩ :=
    ((Lp.memLp f).aefinStronglyMeasurable hp0 hptop).exists_set_sigmaFinite
  set U : Set α := T ∪ Sf with hU_def
  have hUm : MeasurableSet U := hTm.union hSfm
  haveI : SigmaFinite (μ.restrict T) := hTσ
  haveI : SigmaFinite (μ.restrict Sf) := hSfσ
  have hUσ : SigmaFinite (μ.restrict U) := inferInstance
  obtain ⟨gU, hgUmem, hgUb, hgUrep⟩ := Hσ U hUm hUσ
  have hgU_fin : eLpNorm gU q (μ.restrict U) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgUb
  have hTU : T ⊆ U := Set.subset_union_left
  have hcons : gT =ᵐ[μ.restrict T] gU := Hcons hTm hUm hTU hgTmem hgUmem hgTrep hgUrep
  have hnormT : eLpNorm gU q (μ.restrict T) = eLpNorm gT q (μ.restrict T) :=
    eLpNorm_congr_ae hcons.symm
  have hgUT_fin : eLpNorm gU q (μ.restrict T) ≠ ⊤ := by rw [hnormT]; exact hgT_fin
  have hgU_le_c : (eLpNorm gU q (μ.restrict U)).toReal ≤ c :=
    le_csSup hAbdd ⟨U, hUm, hUσ, gU, hgUmem, hgUb, hgUrep, rfl⟩
  have hle : eLpNorm gU q (μ.restrict U) ≤ eLpNorm gU q (μ.restrict T) := by
    apply (ENNReal.toReal_le_toReal hgU_fin hgUT_fin).mp
    rw [hnormT, hNT]; exact hgU_le_c
  have hglue : gU =ᵐ[μ.restrict (U \ T)] 0 := Hglue hTm hUm hTU hq0 hqtop hgUmem hle
  have hfU_mem : MemLp (f : α → ℝ) p (μ.restrict U) := (Lp.memLp f).restrict U
  set fU : Lp ℝ p (μ.restrict U) := hfU_mem.toLp _ with hfU_def
  have hfU_coe : (fU : α → ℝ) =ᵐ[μ.restrict U] (f : α → ℝ) := hfU_mem.coeFn_toLp
  have hextU_eq : ext U hUm fU = f := by
    apply Lp.ext
    have h1 : (ext U hUm fU : α → ℝ) =ᵐ[μ] U.indicator (fU : α → ℝ) := hext U hUm fU
    have h2 : U.indicator (fU : α → ℝ) =ᵐ[μ] U.indicator (f : α → ℝ) :=
      (ae_eq_restrict_iff_indicator_ae_eq hUm).mp hfU_coe
    have hf_aeU : (f : α → ℝ) =ᵐ[μ.restrict Uᶜ] 0 := by
      have hsub : Uᶜ ⊆ Sfᶜ := Set.compl_subset_compl.mpr Set.subset_union_right
      exact ae_mono (Measure.restrict_mono hsub le_rfl) hf_ae
    have h3 : U.indicator (f : α → ℝ) =ᵐ[μ] (f : α → ℝ) :=
      indicator_ae_eq_of_restrict_compl_ae_eq_zero hUm hf_aeU
    exact (h1.trans h2).trans h3
  have hrep : φ f = ∫ a, (fU : α → ℝ) a * gU a ∂(μ.restrict U) := by
    rw [← hextU_eq]; exact hgUrep fU
  have hrep2 : φ f = ∫ a, (f : α → ℝ) a * gU a ∂(μ.restrict U) := by
    rw [hrep]; exact integral_congr_ae (hfU_coe.mono fun a ha => by simp only [ha])
  haveI hHolder : ENNReal.HolderConjugate p q := by
    rw [ENNReal.holderConjugate_iff]
    have hpinv : p⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hp0
    have hqinv : q⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hq0
    have key : (p⁻¹ + q⁻¹).toReal = (1 : ℝ≥0∞).toReal := by
      rw [ENNReal.toReal_add hpinv hqinv, ENNReal.toReal_inv, ENNReal.toReal_inv,
          ENNReal.toReal_one]
      exact hpq.inv_add_inv_eq_one
    have hsum : p⁻¹ + q⁻¹ ≠ ⊤ := by finiteness
    exact (ENNReal.toReal_eq_toReal_iff' hsum (by simp)).mp key
  have hint : Integrable (fun a => (f : α → ℝ) a * gU a) (μ.restrict U) :=
    hfU_mem.integrable_mul hgUmem
  have hsplit := (integral_add_compl hTm hint).symm
  have hcompl0 : ∫ a in Tᶜ, (f : α → ℝ) a * gU a ∂(μ.restrict U) = 0 := by
    rw [Measure.restrict_restrict hTm.compl]
    have hset : Tᶜ ∩ U = U \ T := by rw [Set.inter_comm, Set.diff_eq]
    rw [hset]
    apply integral_eq_zero_of_ae
    filter_upwards [hglue] with a ha
    simp [ha]
  have hTint : ∫ a in T, (f : α → ℝ) a * gU a ∂(μ.restrict U)
      = ∫ a, (f : α → ℝ) a * gT a ∂(μ.restrict T) := by
    rw [Measure.restrict_restrict hTm, Set.inter_eq_left.mpr hTU]
    apply integral_congr_ae
    filter_upwards [hcons] with a ha
    rw [ha]
  rw [hrep2, hsplit, hcompl0, add_zero, hTint]
  have hind : ∀ a, (f : α → ℝ) a * (T.indicator gT) a
      = T.indicator (fun x => (f : α → ℝ) x * gT x) a := by
    intro a; by_cases h : a ∈ T <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  simp_rw [hind]
  exact (integral_indicator hTm).symm

/-- **General-measure Riesz reduction (concrete form).**  Discharges the abstract
    reduction using the concrete Mathlib-only ingredients (`extByZeroCLM`, representer
    consistency/monotonicity, countable-union σ-finiteness, gluing).  Takes only the
    σ-finite Riesz theorem *with the norm bound* (`Hσ`) as a hypothesis — exactly the
    output of `RieszLpDualitySynthesis.riesz_representer_on_sigmaFinite_set` (modulo the
    extension-map used to state the pullback).  Wiring this to the σ-finite chain
    discharges the `riesz_lp_surjective` axiom. -/
theorem riesz_general_of_sigmaFinite
    {p q : ℝ≥0∞} (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal) [Fact (1 ≤ p)]
    (φ : Lp ℝ p μ →L[ℝ] ℝ)
    (Hσ : ∀ (S : Set α) (hS : MeasurableSet S), SigmaFinite (μ.restrict S) →
      ∃ g : α → ℝ, MemLp g q (μ.restrict S) ∧
        eLpNorm g q (μ.restrict S) ≤ ENNReal.ofReal ‖φ‖ ∧
        ∀ f : Lp ℝ p (μ.restrict S),
          φ (RieszLpDualityExtension.extByZeroCLM hS
              (lt_of_lt_of_le zero_lt_one hp1.le).ne' hptop f)
            = ∫ a, (f : α → ℝ) a * g a ∂(μ.restrict S)) :
    ∃ g : α → ℝ, MemLp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1.le).ne'
  refine riesz_general hp1 hptop hpq φ
    (fun S hS => RieszLpDualityExtension.extByZeroCLM hS hp0 hptop)
    (fun S hS f => RieszLpDualityExtension.extByZeroCLM_coeFn hS hp0 hptop f)
    Hσ ?_ ?_ ?_ ?_
  · -- Hmono
    intro S S' hS hS' hSS' gS gS' hgS hgS' hrepS hrepS'
    exact RieszLpDualityConsistency.representer_eLpNorm_mono_of_subset hpq hS hS' hSS' φ
      hgS hgS'
      (RieszLpDualityExtension.extByZeroCLM hS hp0 hptop)
      (RieszLpDualityExtension.extByZeroCLM_coeFn hS hp0 hptop)
      (RieszLpDualityExtension.extByZeroCLM hS' hp0 hptop)
      (RieszLpDualityExtension.extByZeroCLM_coeFn hS' hp0 hptop)
      hrepS hrepS'
  · -- Hcons
    intro S S' hS hS' hSS' gS gS' hgS hgS' hrepS hrepS'
    exact RieszLpDualityConsistency.representer_ae_eq_of_subset hpq hS hS' hSS' φ
      hgS hgS'
      (RieszLpDualityExtension.extByZeroCLM hS hp0 hptop)
      (RieszLpDualityExtension.extByZeroCLM_coeFn hS hp0 hptop)
      (RieszLpDualityExtension.extByZeroCLM hS' hp0 hptop)
      (RieszLpDualityExtension.extByZeroCLM_coeFn hS' hp0 hptop)
      hrepS hrepS'
  · -- HsigU
    exact fun S hSm hSσ => RieszLpDualityIngredients.sigmaFinite_restrict_iUnion hSm hSσ
  · -- Hglue
    exact fun hT hU hTU hq0 hqtop hg hle =>
      RieszLpDualityGluing.eLpNorm_ae_zero_on_diff_of_le hT hU hTU hq0 hqtop hg hle

end RieszLpDualityMaximal

end

#print axioms RieszLpDualityMaximal.riesz_general
#print axioms RieszLpDualityMaximal.riesz_general_of_sigmaFinite
