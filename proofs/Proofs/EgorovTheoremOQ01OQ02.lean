import Proofs.EgorovTheorem
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic

/-
# Lusin's Theorem from Egorov's Theorem

## What This Proves

**Lusin's theorem** is the third of Littlewood's "three principles of real
analysis": *every measurable function is nearly continuous*. Precisely, on a
finite (weakly regular) measure space, for a measurable `f : α → ℝ` and every
`ε > 0` there is a **closed** set `K` with `μ Kᶜ ≤ ε` such that the restriction
of `f` to `K` is continuous.

This file answers the open question attached to the gallery Egorov entry
(`egorov-theorem-oq-01-oq-02`): *derive Lusin's theorem from Egorov plus the
density of continuous functions.* The deduction is exactly the classical one:

1. Continuous functions are dense in `Lᵖ` (Mathlib's
   `BoundedContinuousFunction.toLp_denseRange`), so a measurable `f ∈ Lᵖ` is an
   `Lᵖ`-limit of a sequence `gₙ` of (bounded) **continuous** functions.
2. `Lᵖ` convergence implies convergence in measure
   (`tendstoInMeasure_of_tendsto_Lp`), which yields an almost-everywhere
   convergent subsequence (`TendstoInMeasure.exists_seq_tendsto_ae`).
3. **Egorov's theorem** — taken from the gallery parent
   `EgorovTheorem.egorov_uniform_off_small_set` — upgrades a.e. convergence of
   the `gₙ` to *uniform* convergence off a set of small measure.
4. A uniform limit of continuous functions is continuous
   (`TendstoUniformlyOn.continuousOn`), so `f` is continuous off that small set.
5. Inner regularity of the measure (`MeasurableSet.exists_isClosed_diff_lt`)
   shrinks the "bad" set to a closed `K` of small complement.

The mathematical core — that a sequence of *continuous* functions converging
a.e. forces continuity on a large closed set — is isolated as
`continuousOn_isClosed_of_ae_tendsto`; it is Egorov's theorem plus inner
regularity and is the engine that makes the density argument produce a *closed*
set rather than merely a measurable one.

## Why It Is Not in Mathlib

Mathlib has Egorov's theorem, the density of continuous functions in `Lᵖ`,
convergence in measure, and inner regularity — but it does **not** assemble them
into Lusin's theorem (there is no measure-theoretic Lusin statement in Mathlib;
the `Lusin`-named results there concern descriptive set theory / Polish spaces).
The assembly, the closed-set Egorov core, and the bounded corollary are new.

## Axiom Status

Fully verified, 0 sorries, 0 `axiom` declarations, no `native_decide`. Relies
only on Mathlib's measure theory and the foundational axioms `propext`,
`Classical.choice`, `Quot.sound`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace EgorovLusin

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
  {μ : Measure α}

/-- **Closed-set Egorov core.** If a sequence of *continuous* real functions
`fₙ` converges almost everywhere on a finite-measure measurable set `s` to a
(strongly measurable) function `g`, then for every `ε > 0` there is a **closed**
set `K ⊆ s` with `μ (s \ K) ≤ ε` on which `g` is continuous.

This is the heart of Lusin's theorem: Egorov gives uniform convergence off a
small measurable set, a uniform limit of continuous functions is continuous, and
inner regularity replaces the small measurable set by a closed one. -/
theorem continuousOn_isClosed_of_ae_tendsto [μ.WeaklyRegular]
    {f : ℕ → α → ℝ} {g : α → ℝ} {s : Set α}
    (hcont : ∀ n, Continuous (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K, K ⊆ s ∧ IsClosed K ∧ μ (s \ K) ≤ ENNReal.ofReal ε ∧ ContinuousOn g K := by
  -- Egorov: uniform convergence off a set `t ⊆ s` of measure ≤ ε/2.
  obtain ⟨t, hts, htm, htμ, htU⟩ :=
    EgorovTheorem.egorov_uniform_off_small_set
      (fun n => (hcont n).stronglyMeasurable) hg hsm hs hfg (half_pos hε)
  -- A uniform limit of continuous functions is continuous on `s \ t`.
  have hcontON : ContinuousOn g (s \ t) :=
    htU.continuousOn ((Eventually.of_forall fun n => (hcont n).continuousOn).frequently)
  -- `s \ t` is measurable and of finite measure: approximate it from inside by a closed set.
  have hstm : MeasurableSet (s \ t) := hsm.diff htm
  have hstμ : μ (s \ t) ≠ ∞ := ne_top_of_le_ne_top hs (measure_mono diff_subset)
  obtain ⟨K, hKst, hKc, hKμ⟩ :=
    hstm.exists_isClosed_diff_lt hstμ
      (ne_of_gt (ENNReal.ofReal_pos.mpr (half_pos hε)))
  refine ⟨K, hKst.trans diff_subset, hKc, ?_, hcontON.mono hKst⟩
  -- Measure bound: `s \ K ⊆ t ∪ ((s \ t) \ K)`.
  have hsub : s \ K ⊆ t ∪ ((s \ t) \ K) := by
    intro x hx
    by_cases hxt : x ∈ t
    · exact Or.inl hxt
    · exact Or.inr ⟨⟨hx.1, hxt⟩, hx.2⟩
  calc μ (s \ K) ≤ μ (t ∪ ((s \ t) \ K)) := measure_mono hsub
    _ ≤ μ t + μ ((s \ t) \ K) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add htμ hKμ.le
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-- **Lusin's theorem (`Lᵖ` form).** Let `μ` be a finite, weakly regular measure
and `f : α → ℝ` a strongly measurable function lying in `Lᵖ` (`1 ≤ p < ∞`). Then
for every `ε > 0` there is a **closed** set `K` with `μ Kᶜ ≤ ε` such that `f` is
continuous on `K`. -/
theorem lusin_memLp [NormalSpace α] [μ.WeaklyRegular] [IsFiniteMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : α → ℝ} (hfm : StronglyMeasurable f) (hfLp : MemLp f p μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K, IsClosed K ∧ μ Kᶜ ≤ ENNReal.ofReal ε ∧ ContinuousOn f K := by
  -- Step 1: continuous functions are dense in `Lᵖ`, so `f` is an `Lᵖ`-limit of
  -- bounded continuous functions `gₙ`.
  have hdr : DenseRange (BoundedContinuousFunction.toLp (α := α) (E := ℝ) p μ ℝ) :=
    BoundedContinuousFunction.toLp_denseRange ℝ μ ℝ hp
  have hmem : hfLp.toLp f ∈
      closure (Set.range (BoundedContinuousFunction.toLp (α := α) (E := ℝ) p μ ℝ)) :=
    hdr (hfLp.toLp f)
  rw [mem_closure_iff_seq_limit] at hmem
  obtain ⟨G, hGrange, hGtend⟩ := hmem
  choose g hg using hGrange
  have hgtend : Tendsto (fun n => BoundedContinuousFunction.toLp (α := α) (E := ℝ) p μ ℝ (g n))
      atTop (𝓝 (hfLp.toLp f)) := by
    have hfun : (fun n => BoundedContinuousFunction.toLp (α := α) (E := ℝ) p μ ℝ (g n)) = G :=
      funext hg
    rw [hfun]; exact hGtend
  -- Step 2: `Lᵖ` convergence ⟹ convergence in measure ⟹ a.e. convergent subsequence.
  have hmeas := tendstoInMeasure_of_tendsto_Lp
    (f := fun n => BoundedContinuousFunction.toLp (α := α) (E := ℝ) p μ ℝ (g n))
    (g := hfLp.toLp f) hgtend
  obtain ⟨ns, _hns_mono, hns_ae⟩ := hmeas.exists_seq_tendsto_ae
  -- Replace the `Lᵖ` representatives by the genuine continuous functions `gₙ`.
  have hae : ∀ᵐ x ∂μ, Tendsto (fun k => g (ns k) x) atTop (𝓝 (f x)) := by
    have hcoe_all : ∀ᵐ x ∂μ, ∀ n,
        (BoundedContinuousFunction.toLp (α := α) (E := ℝ) p μ ℝ (g n)) x = g n x :=
      ae_all_iff.mpr fun n => BoundedContinuousFunction.coeFn_toLp p μ ℝ (g n)
    have hcoef : (hfLp.toLp f : α → ℝ) =ᵐ[μ] f := MemLp.coeFn_toLp hfLp
    filter_upwards [hns_ae, hcoe_all, hcoef] with x hx hxcoe hxf
    have hfun : (fun i => (BoundedContinuousFunction.toLp (α := α) (E := ℝ) p μ ℝ (g (ns i))) x)
        = fun k => g (ns k) x := funext fun k => hxcoe (ns k)
    rw [hfun] at hx
    rwa [hxf] at hx
  -- Step 3: apply the closed-set Egorov core on the whole space.
  obtain ⟨K, _, hKc, hKμ, hKcont⟩ :=
    continuousOn_isClosed_of_ae_tendsto
      (f := fun k => (g (ns k) : α → ℝ)) (g := f) (s := Set.univ)
      (fun k => (g (ns k)).continuous) hfm MeasurableSet.univ
      (measure_ne_top μ Set.univ) (hae.mono fun x hx _ => hx) hε
  refine ⟨K, hKc, ?_, hKcont⟩
  simpa only [Set.compl_eq_univ_diff] using hKμ

/-- **Lusin's theorem (bounded form).** A strongly measurable function on a
finite weakly regular measure space that is bounded (`‖f x‖ ≤ C` a.e.) is
continuous off a closed set of arbitrarily small complement. Here membership in
`Lᵖ` is automatic, so no integrability hypothesis is needed. -/
theorem lusin_of_bounded [NormalSpace α] [μ.WeaklyRegular] [IsFiniteMeasure μ]
    {f : α → ℝ} (hfm : StronglyMeasurable f) {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K, IsClosed K ∧ μ Kᶜ ≤ ENNReal.ofReal ε ∧ ContinuousOn f K :=
  lusin_memLp (p := 2) (by simp) hfm (MemLp.of_bound hfm.aestronglyMeasurable C hfC) hε

end EgorovLusin
