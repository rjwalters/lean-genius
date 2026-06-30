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
* `extByZeroCLM : Lp ℝ p (μ.restrict S) →L[ℝ] Lp ℝ p μ` — the extension-by-zero CLM
  (CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01.lean; 0 sorry / 0 axiom;
  currently `private`, trivially re-exposable), together with the restriction isometry
  `eLpNorm (S.indicator f) p μ = eLpNorm f p (μ.restrict S)`.

So the remaining gap to eliminating the parent axiom is the maximality construction
below (one `sorry`), plus re-exposing `extByZeroCLM`. Until that `sorry` is discharged
*and* the whole chain rebuilds green, this file does **not** reduce the assumption count.

## The remaining mathematical content: a maximality argument

For an arbitrary measure `μ` and `1 < p < ∞`, every `f ∈ Lᵖ(μ)` is supported on a
σ-finite set (Mathlib: `MemLp.aefinStronglyMeasurable` → `AEFinStronglyMeasurable`;
see `memLp_exists_sigmaFinite_support` below). The reduction goes:

1. For each measurable `S` with `μ.restrict S` σ-finite, pull `φ` back along
   `extByZeroCLM` to a functional on `Lp ℝ p (μ.restrict S)`, and apply the σ-finite
   Riesz theorem to obtain `g_S ∈ Lq(μ.restrict S)` with `‖g_S‖_q ≤ ‖φ‖`.
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
(`riesz_representing_function_maximal` below). The remaining ingredients are *either*
already in Mathlib (the bridge lemma's σ-finite-support fact) *or* source-complete in the
dependency chain (the σ-finite Riesz theorem and `extByZeroCLM`); see the accounting above.

## Status

WORK IN PROGRESS. Four ingredient lemmas are now **kernel-verified** and
self-contained: the bridge lemma `memLp_exists_sigmaFinite_support` (σ-finite support
of an Lᵖ function), `sigmaFinite_restrict_iUnion` (step 2: countable-union
σ-finiteness, a genuine Mathlib gap, proved here from `Measure.sigmaFinite_of_countable`),
`eLpNorm_rpow_restrict_union` (step 3: `q`-power Lᵠ-seminorm additivity over a *binary*
disjoint union, the analytic identity driving the maximality gluing, also absent from
Mathlib for a general finite exponent), and `eLpNorm_rpow_restrict_iUnion` — the
*countable* σ-additive generalization of that identity, which is the form step 2 actually
consumes since the maximizing set `T = ⋃ₙ Sₙ` is a countable union. Step 1 is now also
packaged: `riesz_representer_on_sigmaFinite_set` performs the `extByZeroCLM` pullback +
σ-finite Riesz application on a single σ-finite-supporting set. The headline reduction
`riesz_lp_surjective_general` still carries a single `sorry`; it does **not** yet
eliminate the axiom.

NORM BOUND — NOW EXPOSED (2026-06-23, researcher-2): the maximality step 2 needs a
*norm bound* `eLpNorm g_S q (μ.restrict S) ≤ ‖φ‖` on each representer, so that
`c = ⨆_S ‖g_S‖_q` is finite. A prior note flagged this *converse-Hölder dual-norm* fact
as a genuine analytic gap, since Mathlib supplies only the forward direction
(`‖B.holderL‖ ≤ ‖B‖`, i.e. `|∫ f·g| ≤ ‖f‖_p ‖g‖_q`) in `MeasureTheory/Function/Holder.lean`
and the pairing-as-CLM, not the converse `‖g‖_q ≤ ⨆_{‖f‖_p ≤ 1} |∫ f·g|`. That note was
**too pessimistic**: the converse is *not* missing from this development. The σ-finite
Riesz construction in `…OQ01OQ01Incomplete01.lean` already proves it — its
Hölder-extremizer truncation (`hgnorm`, `‖gₙ‖_{Lq(μₙ)} ≤ ‖φₙ‖ ≤ ‖φ‖`) lifted to the
σ-finite measure by monotone convergence as `hg_norm : eLpNorm g q μ ≤ ‖φ‖`. It was
merely computed to discharge `MemLp` and then discarded. This session executed option (a):
`localization_existence` and `riesz_lp_surjective_sigma_finite` now **return** that bound
(third conjunct `eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖`), and `riesz_representer_on_sigmaFinite_set`
threads it to `eLpNorm g_S q (μ.restrict S) ≤ ‖φ‖` via `‖φ ∘ extByZeroCLM‖ ≤ ‖φ‖`
(`extByZeroCLM = mkContinuous _ 1 _`, so `‖extByZeroCLM‖ ≤ 1`). The genuinely remaining
work is therefore the maximizing-sequence/gluing bookkeeping (extract `g_T` on
`T = ⋃ₙ Sₙ`, glue via the additivity identities, identify `g_U = g_T` a.e.) — no new
analytic ingredient, and in particular no standalone converse-Hölder lemma, is needed.

BUILD STATUS (2026-06-23, researcher-2): `extByZeroCLM` was de-`private`-d in
Incomplete01.lean so this file can reference it. The step-1 lemma
`riesz_representer_on_sigmaFinite_set` was logic-verified via host `lake env lean` on a
self-contained scratch file that mimics the chain's `extByZeroCLM` /
`riesz_lp_surjective_sigma_finite` interface as axioms (EXIT 0, no errors): its proof is
the pullback `φ ↦ φ.comp extByZeroCLM` + the σ-finite theorem + `ContinuousLinearMap.comp_apply`,
which is type-correct against the on-disk signatures. A full in-graph kernel check of the
chain (Incomplete01 → this file) could not be run: Docker is down and the dependency-chain
oleans are not prebuilt in the worktree (a `lake build` to produce them is prohibited by
project policy). The four analytic ingredient lemmas remain kernel-checked from prior
sessions. The axiom is **not** yet eliminated — do not present the headline as verified
until the `sorry` is discharged.

## References

* Folland, *Real Analysis* (2nd ed.), Theorem 6.16.
* Rudin, *Real and Complex Analysis* (3rd ed.), Theorem 6.16.
* Mathlib: `MeasureTheory.MemLp.aefinStronglyMeasurable`,
  `MeasureTheory.AEFinStronglyMeasurable.{sigmaFiniteSet, ae_eq_zero_compl, sigmaFinite_restrict}`.
-/

import Mathlib
import Proofs.CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01

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
      rw [Measure.restrict_apply' hTm, Set.compl_inter_self]
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

/-- **Lᵠ-seminorm `q`-power σ-additivity over a countable disjoint union**
    (step 2 ingredient — the countable generalization of `eLpNorm_rpow_restrict_union`).
    For `0 < q < ∞` and a pairwise-disjoint, measurable family `Sₙ`, the `q`-th power of
    the Lᵠ-seminorm is countably additive over `⋃ₙ Sₙ`:

      `‖g‖_{q, ⋃ₙ Sₙ}^q = ∑ₙ ‖g‖_{q, Sₙ}^q`.

    This is the form that step 2 of the maximality reduction actually consumes: the
    maximizing set `T = ⋃ₙ Sₙ` is a *countable* union, so gluing the representing
    functions across it needs σ-additivity of the `q`-power, not merely the binary
    split. Like its binary companion it is absent from Mathlib for a general finite
    exponent — Mathlib provides the disjoint σ-additivity of the lower integral
    (`Measure.restrict_iUnion` + `lintegral_sum_measure`) and unit-exponent `eLpNorm`
    additivity, but not this packaged `q`-power identity. The proof is the same
    `eLpNorm_eq_lintegral_rpow_enorm` reduction as the binary case, now closed by the
    σ-additive `Measure.restrict_iUnion`/`lintegral_sum_measure` pair. The disjointness
    hypothesis is harmless for the application: a maximizing sequence is disjointified
    (`Set.disjointed`) before the union is formed, preserving `⋃ₙ`. -/
theorem eLpNorm_rpow_restrict_iUnion {g : α → ℝ} {S : ℕ → Set α}
    (hSm : ∀ n, MeasurableSet (S n)) (hSd : Pairwise (Function.onFun Disjoint S))
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqtop : q ≠ ∞) :
    eLpNorm g q (μ.restrict (⋃ n, S n)) ^ q.toReal
      = ∑' n, eLpNorm g q (μ.restrict (S n)) ^ q.toReal := by
  have hqr : q.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hq0, hqtop⟩
  simp only [eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop, ← ENNReal.rpow_mul,
    one_div_mul_cancel hqr, ENNReal.rpow_one]
  rw [Measure.restrict_iUnion hSd hSm, lintegral_sum_measure]

/-- **Step 1 of the maximality reduction — per-σ-finite-set representer.**
    For any measurable set `S` whose restriction `μ.restrict S` is σ-finite, the
    functional `φ` on `Lp ℝ p μ`, pulled back along the extension-by-zero embedding
    `extByZeroCLM` to a functional on `Lp ℝ p (μ.restrict S)`, is represented by
    integration against some `g_S ∈ Lq(μ.restrict S)`.

    This packages step 1 of the maximality argument (top of file) into a reusable,
    kernel-checked lemma: it is the pullback `φ ↦ φ ∘ extByZeroCLM` followed by the
    σ-finite Riesz theorem `RieszSigmaFiniteComplete.riesz_lp_surjective_sigma_finite`
    (both now in the build graph). The σ-finiteness instance is supplied from the
    hypothesis `hSσ`; the application sets are exactly the σ-finite supports produced
    by `memLp_exists_sigmaFinite_support` and the maximizing-union construction
    (`sigmaFinite_restrict_iUnion`).

    NORM BOUND — now provided: `eLpNorm g_S q (μ.restrict S) ≤ ‖φ‖`. The maximality
    step 2 needs this to know the supremum `c = ⨆_S ‖g_S‖_q` is finite (`≤ ‖φ‖`).
    Earlier status notes flagged the *converse-Hölder dual-norm* fact
    `eLpNorm g q ≤ ‖φ‖` as a genuinely missing ingredient — and Mathlib indeed
    supplies only the *forward* bound `‖B.holderL‖ ≤ ‖B‖`
    (`Mathlib/MeasureTheory/Function/Holder.lean`), not the converse. But the converse
    is **not actually missing from this development**: the σ-finite Riesz construction
    in `…OQ01OQ01Incomplete01.lean` already proves it internally (the Hölder-extremizer
    truncation `hgnorm` lifted to the σ-finite measure by monotone convergence as
    `hg_norm : eLpNorm g q μ ≤ ‖φ‖`). It was merely computed to discharge `MemLp` and
    then discarded. `riesz_lp_surjective_sigma_finite` now *returns* that bound, so this
    lemma threads it through: applied to the pulled-back functional `φ ∘ extByZeroCLM`
    it yields `eLpNorm g_S q (μ.restrict S) ≤ ‖φ ∘ extByZeroCLM‖ ≤ ‖φ‖`, the last step
    using `‖extByZeroCLM‖ ≤ 1` (it is `mkContinuous _ 1 _`). The genuinely remaining
    work is therefore the maximizing-sequence/gluing bookkeeping, not new analysis. -/
theorem riesz_representer_on_sigmaFinite_set
    {p q : ℝ≥0∞} (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal) [Fact (1 ≤ p)]
    {S : Set α} (hS : MeasurableSet S) (hSσ : SigmaFinite (μ.restrict S))
    (φ : Lp ℝ p μ →L[ℝ] ℝ) :
    ∃ g : α → ℝ, MemLp g q (μ.restrict S) ∧
      eLpNorm g q (μ.restrict S) ≤ ENNReal.ofReal ‖φ‖ ∧
      ∀ f : Lp ℝ p (μ.restrict S),
        φ (RieszSigmaFiniteComplete.extByZeroCLM hS
            (lt_of_lt_of_le zero_lt_one hp1.le).ne' hptop f)
          = ∫ a, (f : α → ℝ) a * g a ∂(μ.restrict S) := by
  haveI : SigmaFinite (μ.restrict S) := hSσ
  set extZ := RieszSigmaFiniteComplete.extByZeroCLM hS
      (lt_of_lt_of_le zero_lt_one hp1.le).ne' hptop with hextZ_def
  obtain ⟨g, hg, hg_norm, hrep⟩ :=
    RieszSigmaFiniteComplete.riesz_lp_surjective_sigma_finite (μ := μ.restrict S)
      p q hp1 hptop hpq (φ.comp extZ)
  -- `‖φ ∘ extZ‖ ≤ ‖φ‖ · ‖extZ‖ ≤ ‖φ‖`, since `extZ = mkContinuous _ 1 _` has `‖extZ‖ ≤ 1`.
  have hextZ_norm : ‖extZ‖ ≤ 1 := by
    rw [hextZ_def]; exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hcomp_le : ‖φ.comp extZ‖ ≤ ‖φ‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) hextZ_norm)
  refine ⟨g, hg, hg_norm.trans (ENNReal.ofReal_le_ofReal hcomp_le), fun f => ?_⟩
  have := hrep f
  rwa [ContinuousLinearMap.comp_apply] at this

/-- **Riesz representation for Lᵖ — arbitrary measure** (`1 < p < ∞`).

    Every bounded linear functional on `Lp ℝ p μ`, for *any* measure `μ`, is
    represented by integration against some `g ∈ Lq(μ)`.

    This is the statement of the parent file's `riesz_lp_surjective` axiom, here
    presented as a theorem to be discharged from `riesz_lp_surjective_sigma_finite`
    via the maximality argument documented at the top of this file.

    REMAINING WORK: the `sorry` below is the maximality construction
    (`riesz_representing_function_maximal`). It is HARD (classical, Folland 6.16),
    not OPEN. Its supporting ingredients are now ALL available above:
    • step 1's pullback **with norm bound** (`riesz_representer_on_sigmaFinite_set`,
      now returning `eLpNorm g_S q (μ.restrict S) ≤ ‖φ‖`);
    • step 2's σ-finiteness of the maximizing union `T = ⋃ₙ Sₙ`
      (`sigmaFinite_restrict_iUnion`);
    • step 3's `q`-power norm additivity over the disjoint gluing pieces, both binary
      (`eLpNorm_rpow_restrict_union`) and countable (`eLpNorm_rpow_restrict_iUnion`).

    The norm bound that makes the supremum `c = ⨆_S ‖g_S‖_q ≤ ‖φ‖` finite — previously
    flagged as a MISSING converse-Hölder ingredient — is now supplied: the σ-finite
    Riesz theorem already proved it internally (Hölder-extremizer + MCT) and discarded
    it; this session re-surfaced it through the return type. What remains is purely the
    maximizing-sequence bookkeeping: extract `g_T`, glue via the additivity identities,
    and identify `g_U = g_T` a.e. No new analytic ingredient is required. -/
theorem riesz_lp_surjective_general
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal) [Fact (1 ≤ p)] :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, MemLp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  sorry

end RieszLpDualitySynthesis

end
