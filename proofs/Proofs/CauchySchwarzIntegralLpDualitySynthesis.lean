/-
# Synthesis: Eliminating the `riesz_lp_surjective` Axiom — Full Lᵖ Duality
(cauchy-schwarz-integral-lp-duality-synthesis)

## Goal

The parent file `CauchySchwarzIntegralOQ01OQ01OQ02.lean` states the Lᵖ Riesz
representation for an **arbitrary** measure `μ` (1 < p < ∞) as a single axiom:

    axiom riesz_lp_surjective (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
      (hpq : p.toReal.HolderConjugate q.toReal) :
      ∀ φ : Lp ℝ p μ →L[ℝ] ℝ, ∃ g : α → ℝ, Memℒp g q μ ∧
        ∀ f, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ

This file works toward eliminating that axiom by **reducing the arbitrary-measure
case to the already-proven σ-finite case**, which is the classical strategy of
Folland, *Real Analysis* (2nd ed.), Theorem 6.16 (valid precisely because
`1 < p < ∞`).

## State of the dependency chain (source-complete; not re-build-verified this session)

The reduction in this file targets the σ-finite Riesz theorem. The chain below is
**source-complete** — `grep` finds no `sorry` *tactic* and no `axiom` in any of these
files (the only "sorry" tokens are historical notes in their docstrings). It has,
however, **not** been re-verified under the Docker build wrapper this session (daemon
hung), so "0 sorry / 0 axiom" is a static-source fact, not a fresh kernel check:

* `RieszLpSurjectivity.riesz_lp_surjective_from_rn`  — finite-measure case
  (CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean; 0 sorry / 0 axiom). Radon–Nikodým + Lᵖ.
* `RieszSigmaFinite.riesz_lp_surjective_sigma_finite` — **σ-finite case**
  (CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01.lean; 0 sorry / 0 axiom), built from the
  finite case by spanning-set localization (`localization_existence`) + an Lᵖ density
  extension (both discharged; the docstring "HARD sorry" tags are historical).
* `extByZeroCLM : Lp ℝ p (μ.restrict S) →L[ℝ] Lp ℝ p μ` — the extension-by-zero CLM.
  Now **re-exposed in this file** (below) as a public `def`, rebuilt directly from
  general Mathlib API: `memLp_indicator_iff_restrict` supplies the carrier and
  `eLpNorm_indicator_eq_eLpNorm_restrict` supplies the restriction isometry
  `eLpNorm (S.indicator f) p μ = eLpNorm f p (μ.restrict S)`. Both Mathlib lemmas hold
  for every exponent (no `p ≠ 0` / `p ≠ ∞` side conditions), so the previously-`private`
  gallery helpers in `…Incomplete01.lean` are no longer needed — the "infrastructure
  gap" recorded there for this map is closed. `norm_extByZeroCLM` records that it is an
  isometry.

So the remaining gap to eliminating the parent axiom is **two** `sorry`s: (a) the
*normed* σ-finite Riesz ingredient `riesz_lp_surjective_sigma_finite_normed`
(the σ-finite theorem strengthened to export the operator-norm bound `‖g‖_q ≤ ‖φ‖` —
a mechanical surfacing of an internal `have`, see its docstring), and (b) the maximality
construction `riesz_lp_surjective_general` itself: step 1's `extByZeroCLM` pullback is now
in-file, so what is left is choosing a maximizing sequence, invoking the *normed* σ-finite
Riesz ingredient per piece, and stringing together the now-factored analytic lemmas. Until
both `sorry`s are discharged *and* the whole chain rebuilds green, this file does **not**
reduce the assumption count.

DEPENDENCY SHARPENED (this session): the maximality argument does **not** close over the
plain `RieszSigmaFinite.riesz_lp_surjective_sigma_finite` — that theorem returns only
`MemLp g q μ ∧ (representation)` and *discards* the operator-norm bound `‖g_S‖_q ≤ ‖φ‖`
that step 2 below needs to keep the supremum finite. The bound is already proved inside the
σ-finite chain (`…Incomplete01.lean:791`, `have hg_norm`) but is not in the conclusion;
`riesz_lp_surjective_sigma_finite_normed` is the precise normed restatement that exposes it.

## The remaining mathematical content: a maximality argument

For an arbitrary measure `μ` and `1 < p < ∞`, every `f ∈ Lᵖ(μ)` is supported on a
σ-finite set (Mathlib: `MemLp.aefinStronglyMeasurable` → `AEFinStronglyMeasurable`;
see `memLp_exists_sigmaFinite_support` below). The reduction goes:

1. For each measurable `S` with `μ.restrict S` σ-finite, pull `φ` back along
   `extByZeroCLM` (provided below) to a functional on `Lp ℝ p (μ.restrict S)`, and apply
   the *normed* σ-finite Riesz theorem (`riesz_lp_surjective_sigma_finite_normed`) to
   obtain `g_S ∈ Lq(μ.restrict S)` with `‖g_S‖_q ≤ ‖φ.comp (extByZeroCLM …)‖ ≤ ‖φ‖`
   (the second bound uses `norm_extByZeroCLM`: extension by zero is an isometry, so the
   pullback does not increase the operator norm).
2. Let `c = ⨆_S ‖g_S‖_q` (bounded above by `‖φ‖`, so finite). Pick σ-finite sets
   `S_n` with `‖g_{S_n}‖_q → c`; set `T = ⋃ₙ S_n`. Then `μ.restrict T` is σ-finite
   (countable union of σ-finite pieces — discharged below by
   `sigmaFinite_restrict_iUnion`, a Mathlib gap proved here) and, by uniqueness of
   the representing function, `g_T` realizes the supremum: `‖g_T‖_q = c`.
3. For arbitrary `f ∈ Lᵖ(μ)`, its support `Sf` is σ-finite; put `U = T ∪ Sf`. On `U`,
   `g_U` represents `φ`. Lᵠ-norm additivity over the disjoint pieces `T` and `U \ T`
   plus maximality `‖g_U‖_q ≤ c = ‖g_T‖_q` forces `g_U = g_T` a.e. on `T` and
   `g_U = 0` a.e. on `U \ T`. Hence `φ f = ∫ f · g_U = ∫ f · g_T`, with `g_T`
   extended by `0` off `T`.

The only non-mechanical step is this maximality construction
(`riesz_lp_surjective_general` below). The remaining ingredients are *either* already in
Mathlib (the bridge lemma's σ-finite-support fact) *or* source-complete in the dependency
chain (`extByZeroCLM` and the *plain* σ-finite Riesz theorem) *or* a mechanical export of
an already-proved internal bound (the *normed* σ-finite Riesz ingredient
`riesz_lp_surjective_sigma_finite_normed`); see the accounting above.

## Status

WORK IN PROGRESS. Four ingredient lemmas are now source-complete and self-contained:
the bridge lemma `memLp_exists_sigmaFinite_support` (σ-finite support of an Lᵖ
function), `sigmaFinite_restrict_iUnion` (step 2: countable-union σ-finiteness, a
genuine Mathlib gap, proved here from `Measure.sigmaFinite_of_countable`),
`eLpNorm_rpow_restrict_union` (step 3: `q`-power Lᵠ-seminorm additivity over a
disjoint union, the analytic identity driving the maximality gluing, also absent from
Mathlib for a general finite exponent), and `eLpNorm_restrict_eq_zero_of_le_restrict_left`
(step 3's a.e.-identification *mechanism*: from the maximality bound and that additivity
identity, the representing function is forced to vanish a.e. off the maximal set). Step 4's
uniqueness of the representing function is now factored too —
`memLp_ae_eq_of_forall_setIntegral_eq` (and its vanishing form
`memLp_ae_eq_zero_of_forall_setIntegral_eq_zero`): two Lᵠ functions representing the same
functional agree a.e., obtained by testing against finite-measure-set indicators and
applying Mathlib's `setIntegral`-uniqueness engine. This is what realizes the supremum on
the maximizing hull `T` and identifies `g_U` with `g_T` on overlaps. Step 1 is in-file too:
`extByZeroCLM` (the extension-by-zero pullback CLM) and its isometry `norm_extByZeroCLM` are
re-exposed here, rebuilt from general Mathlib API. Two `sorry`s remain: (a)
`riesz_lp_surjective_sigma_finite_normed` — the normed σ-finite Riesz ingredient,
mechanically surfacing the operator-norm bound already proved inside the σ-finite chain
(`…Incomplete01.lean:791`); and (b) the headline reduction `riesz_lp_surjective_general`,
the remaining maximality *plumbing* (choosing a maximizing sequence, invoking the *normed*
σ-finite Riesz ingredient per piece via this pullback, instantiating uniqueness at
indicators, and stitching together the now-factored facts) — neither yet eliminates the
axiom.

NOT BUILD-VERIFIED: the local Docker build wrapper has been hanging and Aristotle is
unavailable, so `sigmaFinite_restrict_iUnion` is source-complete but its proof has not
been kernel-checked locally; the deployer build-gate is the verifier. Do not present
this file as verified until both `sorry`s are discharged and the file builds.

## References

* Folland, *Real Analysis* (2nd ed.), Theorem 6.16.
* Rudin, *Real and Complex Analysis* (3rd ed.), Theorem 6.16.
* Mathlib: `MeasureTheory.MemLp.aefinStronglyMeasurable`,
  `MeasureTheory.AEFinStronglyMeasurable.{sigmaFiniteSet, ae_eq_zero_compl, sigmaFinite_restrict}`.
-/

import Mathlib

noncomputable section

open MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszLpDualitySynthesis

/-- **Bridge lemma.** For `0 < p < ∞`, every `f ∈ Lᵖ(μ)` is a.e. supported on a
    measurable set `S` whose restricted measure `μ.restrict S` is σ-finite: `f = 0`
    a.e. on the complement of `S`.

    This is the ingredient that reduces the *arbitrary-measure* Riesz representation
    to the *σ-finite* case, and it resolves what the earlier sigma-finite file flagged
    as a "Lean infrastructure gap": Mathlib already supplies it via
    `MemLp.aefinStronglyMeasurable`. -/
theorem memLp_exists_sigmaFinite_support
    {f : α → ℝ} {p : ℝ≥0∞} (hf : MemLp f p μ) (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    ∃ S : Set α, MeasurableSet S ∧ SigmaFinite (μ.restrict S) ∧ f =ᵐ[μ.restrict Sᶜ] 0 := by
  have h := hf.aefinStronglyMeasurable hp0 hptop
  exact ⟨h.sigmaFiniteSet, h.measurableSet, h.sigmaFinite_restrict, h.ae_eq_zero_compl⟩

/-- **σ-finiteness of a restriction is closed under countable unions.**
    If each `μ.restrict (S n)` is σ-finite (with the `S n` measurable), then so is
    `μ.restrict (⋃ n, S n)`.

    Mathlib supplies only the *binary*-union instance
    (`SigmaFinite (μ.restrict (s ∪ t))` in
    `Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`); the countable version
    is **not** in Mathlib (confirmed by source search) yet is exactly step 2 of the
    maximality reduction below — forming the σ-finite set `T = ⋃ₙ Sₙ` from a
    maximizing sequence `Sₙ`. The measurability hypothesis is harmless for the
    application: the σ-finite supports produced by
    `AEFinStronglyMeasurable.sigmaFiniteSet` are measurable.

    Proof: each `μ.restrict (S n)` has a countable family of finite-measure spanning
    sets `spanningSets (μ.restrict (S n)) k`. The countable family
    `{spanningSets (μ.restrict (S n)) k ∩ S n}ₙ,ₖ ∪ {(⋃ₙ Sₙ)ᶜ}` covers `univ`, and
    each member has finite `μ.restrict (⋃ₙ Sₙ)`-measure (via `restrict_apply'`, which
    needs only the `S n` measurable, not the spanning sets). Apply
    `Measure.sigmaFinite_of_countable`. -/
theorem sigmaFinite_restrict_iUnion {S : ℕ → Set α}
    (hSm : ∀ n, MeasurableSet (S n))
    (hS : ∀ n, SigmaFinite (μ.restrict (S n))) :
    SigmaFinite (μ.restrict (⋃ n, S n)) := by
  haveI hSi : ∀ n, SigmaFinite (μ.restrict (S n)) := hS
  have hTm : MeasurableSet (⋃ n, S n) := MeasurableSet.iUnion hSm
  refine Measure.sigmaFinite_of_countable
      (S := Set.range (fun p : ℕ × ℕ => spanningSets (μ.restrict (S p.1)) p.2 ∩ S p.1)
            ∪ {(⋃ n, S n)ᶜ})
      ((Set.countable_range _).union (Set.countable_singleton _)) ?_ ?_
  · rintro s (⟨p, rfl⟩ | rfl)
    · show (μ.restrict (⋃ n, S n))
          (spanningSets (μ.restrict (S p.1)) p.2 ∩ S p.1) < ∞
      have hsub : spanningSets (μ.restrict (S p.1)) p.2 ∩ S p.1 ⊆ ⋃ n, S n :=
        Set.inter_subset_right.trans (Set.subset_iUnion S p.1)
      rw [Measure.restrict_apply' hTm, Set.inter_eq_left.2 hsub,
        ← Measure.restrict_apply' (hSm p.1)]
      exact measure_spanningSets_lt_top _ _
    · show (μ.restrict (⋃ n, S n)) ((⋃ n, S n)ᶜ) < ∞
      rw [Measure.restrict_apply' hTm]
      simp
  · rw [Set.sUnion_union, Set.sUnion_range, Set.sUnion_singleton]
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ ⋃ n, S n
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
      have hxk : x ∈ ⋃ k, spanningSets (μ.restrict (S n)) k := by
        rw [iUnion_spanningSets]; exact Set.mem_univ x
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hxk
      exact Set.mem_union_left _ (Set.mem_iUnion.2 ⟨(n, k), hk, hn⟩)
    · exact Set.mem_union_right _ hx

/-- **Lᵠ-seminorm `q`-power additivity over a disjoint union** (step 3 ingredient).
    For `0 < q < ∞` and disjoint measurable sets `A`, `B`, the `q`-th power of the
    Lᵠ-seminorm is additive over `A ∪ B`:

      `‖g‖_{q, A ∪ B}^q = ‖g‖_{q, A}^q + ‖g‖_{q, B}^q`.

    This is the analytic identity behind the maximality *gluing* in step 3 below.
    Combined with the maximality bound `‖g_U‖_q ≤ c = ‖g_T‖_q`, additivity over the
    disjoint pieces `T` and `U \ T` (with `U = T ∪ (U \ T)`) gives
    `‖g_U‖_{q,T}^q + ‖g_U‖_{q,U\T}^q = ‖g_U‖_{q,U}^q ≤ ‖g_T‖_{q,T}^q`; since the
    representing function on `T` is unique (`‖g_U‖_{q,T} = ‖g_T‖_q`), the `U \ T`
    contribution is forced to `0`, so `g_U = 0` a.e. off `T`.

    Mathlib supplies the underlying disjoint additivity of the lower integral
    (`Measure.restrict_union` + `lintegral_add_measure`) and the unit-exponent
    measure-additivity `eLpNorm_one_add_measure`, but **not** this packaged
    `q`-power identity for `eLpNorm` at a general finite exponent (source-searched).
    The `q`-th power is the right invariant to state it on: the seminorm itself is
    only *sub*additive (Minkowski, `eLpNorm_add_le`), whereas its `q`-th power
    splits exactly over disjoint supports. -/
theorem eLpNorm_rpow_restrict_union {g : α → ℝ} {A B : Set α}
    (hB : MeasurableSet B) (hAB : Disjoint A B)
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqtop : q ≠ ∞) :
    eLpNorm g q (μ.restrict (A ∪ B)) ^ q.toReal
      = eLpNorm g q (μ.restrict A) ^ q.toReal
        + eLpNorm g q (μ.restrict B) ^ q.toReal := by
  have hqr : q.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hq0, hqtop⟩
  simp only [eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop, ← ENNReal.rpow_mul,
    one_div_mul_cancel hqr, ENNReal.rpow_one]
  rw [Measure.restrict_union hAB hB, lintegral_add_measure]

/-- **Maximality forces vanishing off the maximal set** (step 3 mechanism).
    For `0 < q < ∞` and disjoint measurable sets `A`, `B`, if the Lᵠ-seminorm of `g`
    over `A ∪ B` does not exceed its Lᵠ-seminorm over `A` alone — and the latter is
    finite (`g ∈ Lᵠ` there) — then `g` vanishes a.e. on the disjoint piece `B`.

    This is precisely the a.e.-identification step in the maximality argument: with
    `A = T` the maximizing σ-finite set and `B = U \ T`, the maximality bound
    `‖g_U‖_{q,U} ≤ c = ‖g_T‖_{q,T} = ‖g_U‖_{q,T}` (uniqueness on `T`) feeds this lemma
    to force `g_U = 0` a.e. on `U \ T`, so the representing function on `U` agrees with
    the one on `T` extended by zero.

    Proof: monotonicity of `· ^ q.toReal` turns the seminorm bound into a bound on the
    `q`-powers; `eLpNorm_rpow_restrict_union` splits the `A ∪ B` power as
    `‖g‖_{q,A}^q + ‖g‖_{q,B}^q`, and cancelling the finite `A`-term
    (`ENNReal.add_le_add_iff_left`) forces `‖g‖_{q,B}^q ≤ 0`, hence `‖g‖_{q,B} = 0`
    (`ENNReal.rpow_eq_zero_iff_of_pos`), hence `g =ᵐ 0` on `B` (`eLpNorm_eq_zero_iff`).
    Mathlib has the pieces but not this packaged maximality-to-vanishing step. -/
theorem eLpNorm_restrict_eq_zero_of_le_restrict_left
    {g : α → ℝ} {A B : Set α}
    (hB : MeasurableSet B) (hAB : Disjoint A B)
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqtop : q ≠ ∞)
    (hgmeas : AEStronglyMeasurable g (μ.restrict B))
    (hA_fin : eLpNorm g q (μ.restrict A) ≠ ∞)
    (hle : eLpNorm g q (μ.restrict (A ∪ B)) ≤ eLpNorm g q (μ.restrict A)) :
    g =ᵐ[μ.restrict B] 0 := by
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have hadd := eLpNorm_rpow_restrict_union (μ := μ) (g := g) hB hAB hq0 hqtop
  have hmono : eLpNorm g q (μ.restrict (A ∪ B)) ^ q.toReal
      ≤ eLpNorm g q (μ.restrict A) ^ q.toReal :=
    ENNReal.rpow_le_rpow hle hqr.le
  rw [hadd] at hmono
  have hAfin' : eLpNorm g q (μ.restrict A) ^ q.toReal ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg hqr.le hA_fin).ne
  have hble : eLpNorm g q (μ.restrict B) ^ q.toReal ≤ 0 := by
    have h : eLpNorm g q (μ.restrict A) ^ q.toReal
          + eLpNorm g q (μ.restrict B) ^ q.toReal
        ≤ eLpNorm g q (μ.restrict A) ^ q.toReal + 0 := by rwa [add_zero]
    exact (ENNReal.add_le_add_iff_left hAfin').mp h
  have hbz : eLpNorm g q (μ.restrict B) ^ q.toReal = 0 := le_antisymm hble (zero_le _)
  have hb0 : eLpNorm g q (μ.restrict B) = 0 :=
    (ENNReal.rpow_eq_zero_iff_of_pos hqr).mp hbz
  exact (eLpNorm_eq_zero_iff hgmeas hq0).mp hb0

/-- An Lᵠ function with `1 ≤ q` is integrable on every finite-measure set: restricting
    to `s` gives a finite measure on which `Lᵠ ⊆ L¹`. Helper for the uniqueness lemmas. -/
private theorem integrableOn_of_memLp {ν : Measure α} {g : α → ℝ} {q : ℝ≥0∞}
    (hq1 : 1 ≤ q) (hg : MemLp g q ν) {s : Set α} (hνs : ν s < ∞) :
    IntegrableOn g s ν := by
  haveI : IsFiniteMeasure (ν.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hνs⟩
  exact (hg.restrict s).integrable hq1

/-- **Uniqueness of the Lᵠ representing function — vanishing form** (step 4 ingredient).
    For `1 ≤ q < ∞`, a function `g ∈ Lᵠ(ν)` that integrates to zero over *every*
    finite-measure set is zero a.e.

    In the maximality argument this is the engine that turns "represents the zero
    functional" into "is a.e. zero": testing the representation `∀ f, ∫ f·g = 0`
    against the indicators of finite-measure sets (which lie in `Lᵖ` because the
    exponent is finite) yields exactly the `setIntegral`-vanishing hypothesis below,
    so the representing function attached to a σ-finite piece is determined a.e. — the
    fact step 4 needs to identify `g_U` with `g_T` on the overlap and to realize the
    supremum on the maximizing hull `T`.

    Mathlib supplies the general `setIntegral`-uniqueness engine
    (`AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero`), but not this
    Lᵠ-packaged corollary: the only work is producing the `AEFinStronglyMeasurable`
    witness (`MemLp.aefinStronglyMeasurable`, valid since `q ≠ 0, ∞`) and the
    finite-set integrability side condition (`integrableOn_of_memLp`). No σ-finiteness
    of `ν` is needed — the engine localizes to the function's own σ-finite support. -/
theorem memLp_ae_eq_zero_of_forall_setIntegral_eq_zero {ν : Measure α}
    {g : α → ℝ} {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hqtop : q ≠ ∞) (hg : MemLp g q ν)
    (hzero : ∀ s : Set α, MeasurableSet s → ν s < ∞ → ∫ a in s, g a ∂ν = 0) :
    g =ᵐ[ν] 0 := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  exact (hg.aefinStronglyMeasurable hq0 hqtop).ae_eq_zero_of_forall_setIntegral_eq_zero
    (fun s _ hνs => integrableOn_of_memLp hq1 hg hνs) hzero

/-- **Uniqueness of the Lᵠ representing function — agreement form** (step 4 ingredient).
    For `1 ≤ q < ∞`, two functions `g₁, g₂ ∈ Lᵠ(ν)` with equal integrals over every
    finite-measure set agree a.e.

    This is the form consumed directly in the maximality argument: when both `g₁` and
    `g₂` represent the same bounded functional on `Lᵖ(ν)` (so `∫ f·g₁ = φ f = ∫ f·g₂`
    for all `f`), instantiating at indicators of finite-measure sets gives the
    `setIntegral`-agreement hypothesis, hence `g₁ =ᵐ g₂`. With `ν = μ.restrict Sₙ` and
    `Sₙ ⊆ T` this is what forces `g_{Sₙ}` to coincide with `g_T` on `Sₙ`, so that the
    supremum `c = ⨆_S ‖g_S‖_q` is realized on the hull `T`.

    Mathlib's `AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq` provides the
    engine; this packages it for Lᵠ functions. -/
theorem memLp_ae_eq_of_forall_setIntegral_eq {ν : Measure α}
    {g₁ g₂ : α → ℝ} {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hqtop : q ≠ ∞)
    (hg₁ : MemLp g₁ q ν) (hg₂ : MemLp g₂ q ν)
    (h : ∀ s : Set α, MeasurableSet s → ν s < ∞ →
      ∫ a in s, g₁ a ∂ν = ∫ a in s, g₂ a ∂ν) :
    g₁ =ᵐ[ν] g₂ := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  exact (hg₁.aefinStronglyMeasurable hq0 hqtop).ae_eq_of_forall_setIntegral_eq
    (fun s _ hνs => integrableOn_of_memLp hq1 hg₁ hνs)
    (fun s _ hνs => integrableOn_of_memLp hq1 hg₂ hνs) h
    (hg₂.aefinStronglyMeasurable hq0 hqtop)

/-- **Extension-by-zero CLM** (step 1 ingredient): the isometric embedding
    `Lp ℝ p (μ.restrict S) →L[ℝ] Lp ℝ p μ` sending `f` to its extension by zero
    `S.indicator f`.

    This is the operator that pulls a bounded functional `φ` on `Lp ℝ p μ` back to a
    functional `φ.comp (extByZeroCLM hS)` on the σ-finite piece `Lp ℝ p (μ.restrict S)`,
    where `riesz_lp_surjective_sigma_finite` applies — step 1 of the maximality argument
    for the headline reduction below.

    Both ingredients of the construction are now plain Mathlib lemmas:
    `memLp_indicator_iff_restrict` (`MemLp (S.indicator f) p μ ↔ MemLp f p (μ.restrict S)`)
    supplies the carrier, and `eLpNorm_indicator_eq_eLpNorm_restrict`
    (`eLpNorm (S.indicator f) p μ = eLpNorm f p (μ.restrict S)`) supplies the isometry.
    Both hold for **every** exponent with no `p ≠ 0` / `p ≠ ∞` side conditions, so the
    map needs only `[Fact (1 ≤ p)]`. This **retires the "Lean infrastructure gap"** the
    earlier σ-finite file flagged for re-exposing this CLM: the only previously-private
    helpers (`memLp_indicator_of_restrict_loc`, `eLpNorm_indicator_eq_restrict_loc`) are
    now subsumed by general Mathlib API. -/
noncomputable def extByZeroCLM {S : Set α} (hS : MeasurableSet S)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Lp ℝ p (μ.restrict S) →L[ℝ] Lp ℝ p μ :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).toLp _
      map_add' := fun f₁ f₂ => by
        rw [Lp.ext_iff]
        filter_upwards [
          ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp (f₁ + f₂))).coeFn_toLp,
          ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f₁)).coeFn_toLp,
          ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f₂)).coeFn_toLp,
          Lp.coeFn_add
            (((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f₁)).toLp _)
            (((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f₂)).toLp _),
          (Measure.ae_restrict_iff' hS).mp (Lp.coeFn_add f₁ f₂)]
          with a h12 h1 h2 hadd hinner
        rw [h12, hadd, h1, h2]
        simp only [Set.indicator_apply, Pi.add_apply]
        split_ifs with ha
        · exact hinner ha
        · ring
      map_smul' := fun c f => by
        rw [Lp.ext_iff]
        filter_upwards [
          ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp (c • f))).coeFn_toLp,
          ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).coeFn_toLp,
          Lp.coeFn_smul c
            (((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).toLp _),
          (Measure.ae_restrict_iff' hS).mp (Lp.coeFn_smul c f)]
          with a hcf hf hsmul hinner
        rw [hcf, hsmul, hf, RingHom.id_apply]
        simp only [Set.indicator_apply, Pi.smul_apply]
        split_ifs with ha
        · simp [hinner ha]
        · simp }
    1
    (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      have hh := (memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)
      have heq : ‖hh.toLp _‖ = ‖f‖ := by
        simp only [Lp.norm_def]
        congr 1
        rw [eLpNorm_congr_ae hh.coeFn_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hS]
      exact heq.le)

/-- The extension-by-zero CLM acts pointwise (a.e.) as `S.indicator`. -/
theorem extByZeroCLM_coeFn_ae {S : Set α} (hS : MeasurableSet S)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Lp ℝ p (μ.restrict S)) :
    (extByZeroCLM hS f : α → ℝ) =ᵐ[μ] S.indicator (f : α → ℝ) :=
  ((memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)).coeFn_toLp

/-- **`extByZeroCLM` is an isometry.** Extension by zero preserves the Lᵖ-norm
    (`‖S.indicator f‖_{Lp μ} = ‖f‖_{Lp (μ.restrict S)}`), so pulling a functional back
    along it does not increase its operator norm: `‖φ.comp (extByZeroCLM hS)‖ ≤ ‖φ‖`.
    This uniform bound is what makes the supremum over σ-finite pieces in the maximality
    argument finite. -/
theorem norm_extByZeroCLM {S : Set α} (hS : MeasurableSet S)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Lp ℝ p (μ.restrict S)) :
    ‖extByZeroCLM hS f‖ = ‖f‖ := by
  simp only [Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (extByZeroCLM_coeFn_ae hS f),
    eLpNorm_indicator_eq_eLpNorm_restrict hS]

/-- **Normed σ-finite Riesz representation** (step 0 ingredient — *the* dependency of
    the maximality argument). For a σ-finite measure `μ` and `1 < p < ∞`, every bounded
    functional `φ` on `Lp ℝ p μ` is represented by some `g ∈ Lᵠ(μ)` whose `Lᵠ`-seminorm
    is controlled by the operator norm: `eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖`.

    This is the precise strengthening of `RieszSigmaFinite.riesz_lp_surjective_sigma_finite`
    that the headline reduction below actually consumes. The plain σ-finite theorem returns
    only `MemLp g q μ ∧ (representation)`; it *discards* the operator-norm bound. But that
    bound is **exactly** what makes the maximality supremum `c = ⨆_S ‖g_S‖_q` finite
    (`c ≤ ‖φ‖`), so without it the maximality construction cannot even get off the ground.

    The bound is **not new mathematics** — it is already established inside the σ-finite
    proof: see `RieszSigmaFiniteComplete.localization_existence`
    (`CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01.lean:791`, the named
    `have hg_norm : eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖`), where it is proved via the
    Hölder-extremizer estimate `‖g_k‖_q ≤ ‖φ ∘ extByZeroCLM‖ ≤ ‖φ‖` on truncations,
    promoted through the monotone-convergence limit. The `MemLp g q μ` conclusion is then
    derived *from* this very bound (`hg_lq := ⟨hg_asm, (hg_norm.trans_lt ofReal_lt_top).ne⟩`).
    So discharging this `sorry` is the **mechanical export** of an existing internal `have`
    to the conclusion — HARD-but-known (classical, Folland 6.16 norm half), not OPEN. It is
    the cleanest Aristotle / next-session target on the critical path. -/
theorem riesz_lp_surjective_sigma_finite_normed
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal)
    [SigmaFinite μ] [Fact (1 ≤ p)] (φ : Lp ℝ p μ →L[ℝ] ℝ) :
    ∃ g : α → ℝ, MemLp g q μ ∧ eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  sorry

/-- **Riesz representation for Lᵖ — arbitrary measure** (`1 < p < ∞`).

    Every bounded linear functional on `Lp ℝ p μ`, for *any* measure `μ`, is
    represented by integration against some `g ∈ Lq(μ)`.

    This is the statement of the parent file's `riesz_lp_surjective` axiom, here
    presented as a theorem to be discharged from `riesz_lp_surjective_sigma_finite_normed`
    via the maximality argument documented at the top of this file.

    KEY DEPENDENCY (sharpened this session): the maximality argument consumes the
    *normed* σ-finite Riesz theorem `riesz_lp_surjective_sigma_finite_normed` above, not
    the plain one — it needs the operator-norm bound `‖g_S‖_q ≤ ‖φ‖` to keep the supremum
    `c = ⨆_S ‖g_S‖_q` finite. The plain `RieszSigmaFinite.riesz_lp_surjective_sigma_finite`
    discards that bound, so it is insufficient as stated; see the normed wrapper's docstring
    for why the bound is already proved internally and only needs surfacing.

    REMAINING WORK: the `sorry` below is the maximality construction
    (`riesz_representing_function_maximal`). It is HARD (classical, Folland 6.16),
    not OPEN. Its analytic core is now factored out and source-complete above:
    step 2's σ-finiteness of the maximizing union `T = ⋃ₙ Sₙ`
    (`sigmaFinite_restrict_iUnion`), step 3's `q`-power norm additivity over the
    disjoint gluing pieces `T` and `U \ T` (`eLpNorm_rpow_restrict_union`), and the
    a.e.-identification mechanism that turns the maximality bound into vanishing off
    `T` (`eLpNorm_restrict_eq_zero_of_le_restrict_left`), step 4's uniqueness of the
    representing function (`memLp_ae_eq_of_forall_setIntegral_eq`), and step 1's
    extension-by-zero pullback `extByZeroCLM` (with isometry `norm_extByZeroCLM`). What
    remains is the *plumbing* that strings them together: pulling `φ` back along
    `extByZeroCLM` per σ-finite set to invoke the σ-finite Riesz theorem, choosing a
    maximizing sequence, and extracting `g_T` — after which `g_U = g_T` a.e. follows from
    the now-available factored lemmas. -/
theorem riesz_lp_surjective_general
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal) [Fact (1 ≤ p)] :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, MemLp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  sorry

end RieszLpDualitySynthesis

end
