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

## State of the dependency chain

The reduction in this file targets the σ-finite Riesz theorem. The chain below is
`sorry`-free and `axiom`-free (the only "sorry" tokens are historical notes in
docstrings):

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

The maximality construction that reduces the arbitrary-measure case to this σ-finite
theorem is `RieszLpDualityMaximal.riesz_general` (a standalone, Mathlib-only file);
`riesz_lp_surjective_general` below wires it to the chain. Both are `sorry`-free.

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

The only non-mechanical step is this maximality construction, discharged in the
standalone `RieszLpDualityMaximal.riesz_general`. The remaining ingredients are *either*
already in Mathlib (the bridge lemma's σ-finite-support fact) *or* proved in the
dependency chain (the σ-finite Riesz theorem and `extByZeroCLM`); see the accounting above.

## Status

**RESOLVED (2026-07-08, researcher-4).** The headline reduction
`riesz_lp_surjective_general` is **fully discharged and kernel-verified** — a
complete Docker build of the whole chain (Ingredients → Consistency → Gluing →
Extension → Norm/Loc/Maximal → this file) succeeds, and `#print axioms` reports
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `Lean.ofReduceBool`).
The discharge feeds the `RieszSigmaFiniteComplete.extByZeroCLM` twin into the
ext-agnostic Folland-6.16 maximality assembly `RieszLpDualityMaximal.riesz_general`,
supplying the a.e. `extByZeroCLM_coeFn` identity and the four
Consistency/Ingredients/Gluing ingredient lemmas. Eliminating the **parent gallery
axiom** `riesz_lp_surjective` is a separate follow-on (import-direction: it lives
upstream in `…OQ01OQ01OQ02.lean` and cannot import this file, so it needs a
re-export or gallery re-point). The historical WIP notes below are retained for
provenance.

HISTORICAL NOTE (provenance). The step-1/step-2/step-3 ingredients now used by the
reduction were built incrementally: the bridge lemma `memLp_exists_sigmaFinite_support`
(σ-finite support of an Lᵖ function), `sigmaFinite_restrict_iUnion` (countable-union
σ-finiteness, a genuine Mathlib gap proved here from `Measure.sigmaFinite_of_countable`),
`eLpNorm_rpow_restrict_union` / `eLpNorm_rpow_restrict_iUnion` (`q`-power Lᵠ-seminorm
additivity over binary / countable disjoint unions, also absent from Mathlib for a general
finite exponent), and the step-1 pullback `riesz_representer_on_sigmaFinite_set`. The
per-representer norm bound `eLpNorm g_S q (μ.restrict S) ≤ ‖φ‖` — once flagged as a missing
converse-Hölder ingredient — was in fact already produced internally by the σ-finite Riesz
construction (Hölder-extremizer truncation + monotone convergence) and merely discarded;
`riesz_lp_surjective_sigma_finite` now returns it, and `riesz_representer_on_sigmaFinite_set`
threads it through `‖φ ∘ extByZeroCLM‖ ≤ ‖φ‖`. The maximizing-sequence/gluing assembly that
consumes these was then factored into the standalone `RieszLpDualityMaximal.riesz_general`
(ext-agnostic; takes the σ-finite representer as an explicit hypothesis), so it verifies
Mathlib-only without the heavy σ-finite build.

## References

* Folland, *Real Analysis* (2nd ed.), Theorem 6.16.
* Rudin, *Real and Complex Analysis* (3rd ed.), Theorem 6.16.
* Mathlib: `MeasureTheory.MemLp.aefinStronglyMeasurable`,
  `MeasureTheory.AEFinStronglyMeasurable.{sigmaFiniteSet, ae_eq_zero_compl, sigmaFinite_restrict}`.
-/

import Mathlib
import Proofs.CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01
import Proofs.CauchySchwarzIntegralLpDualityMaximal

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

/-- **Monotonicity of the `q`-power Lᵠ-seminorm under set inclusion** (step 2 ingredient).
    For `0 < q < ∞` and measurable `A ⊆ B`, the `q`-th power of the Lᵠ-seminorm is
    monotone in the restriction set:

      `‖g‖_{q, A}^q ≤ ‖g‖_{q, B}^q`.

    This is the order-theoretic content that makes the maximality *supremum*
    `c = ⨆_S ‖g_S‖_q` well-behaved: enlarging the σ-finite support set can only increase
    the representing function's norm, so a maximizing *sequence* can be replaced by its
    increasing union without loss. It is an immediate corollary of the disjoint additivity
    `eLpNorm_rpow_restrict_union` applied to the decomposition `B = A ∪ (B \ A)`: the
    `(B \ A)`-contribution is a nonnegative `ℝ≥0∞`, so it only adds. Stated on the
    `q`-power (not the seminorm itself) for the same reason as its additive companion —
    the `q`-power splits exactly over disjoint supports while the seminorm is merely
    subadditive. -/
theorem eLpNorm_rpow_restrict_mono {g : α → ℝ} {A B : Set α}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqtop : q ≠ ∞) :
    eLpNorm g q (μ.restrict A) ^ q.toReal
      ≤ eLpNorm g q (μ.restrict B) ^ q.toReal := by
  have hdiff : MeasurableSet (B \ A) := hB.diff hA
  have hdisj : Disjoint A (B \ A) :=
    Set.disjoint_left.2 (fun x hxA hxD => hxD.2 hxA)
  have hunion : A ∪ (B \ A) = B := Set.union_diff_cancel hAB
  have key := eLpNorm_rpow_restrict_union (μ := μ) (g := g) (A := A) (B := B \ A)
    hdiff hdisj hq0 hqtop
  rw [hunion] at key
  rw [key]
  exact le_self_add

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

    This is the statement of the parent file's `riesz_lp_surjective` axiom (modulo the
    `Memℒp`/`MemLp` spelling), here **discharged** as a theorem from the σ-finite Riesz
    theorem via the Folland-6.16 maximality argument documented at the top of this file.
    No `sorry`: it feeds the σ-finite chain's extension CLM and representer into the
    ext-agnostic assembly `RieszLpDualityMaximal.riesz_general`.

    The maximality construction (HARD, classical, not OPEN) draws on ingredients that are
    all available: step 1's pullback **with norm bound** (`riesz_representer_on_sigmaFinite_set`,
    returning `eLpNorm g_S q (μ.restrict S) ≤ ‖φ‖`); step 2's σ-finiteness of the maximizing
    union `T = ⋃ₙ Sₙ` (`sigmaFinite_restrict_iUnion`); and step 3's `q`-power norm additivity
    over the disjoint gluing pieces (`eLpNorm_rpow_restrict_union` / `_iUnion`).

    The norm bound that makes the supremum `c = ⨆_S ‖g_S‖_q ≤ ‖φ‖` finite — once flagged as a
    missing converse-Hölder ingredient — is supplied by the σ-finite Riesz theorem itself
    (Hölder-extremizer + MCT), re-surfaced through its return type. -/
theorem riesz_lp_surjective_general
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal) [Fact (1 ≤ p)] :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, MemLp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  intro φ
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1.le).ne'
  -- Feed the σ-finite-chain extension CLM (against which
  -- `riesz_representer_on_sigmaFinite_set` produces its representation) into the
  -- ext-agnostic Folland-6.16 maximality assembly `riesz_general`.
  refine RieszLpDualityMaximal.riesz_general hp1 hptop hpq φ
    (fun S hS => RieszSigmaFiniteComplete.extByZeroCLM hS hp0 hptop)
    (fun S hS f => RieszSigmaFiniteComplete.extByZeroCLM_coeFn hS hp0 hptop f)
    (fun S hS hSσ => riesz_representer_on_sigmaFinite_set hp1 hptop hpq hS hSσ φ)
    ?_ ?_ ?_ ?_
  · -- Hmono
    intro S S' hS hS' hSS' gS gS' hgS hgS' hrepS hrepS'
    exact RieszLpDualityConsistency.representer_eLpNorm_mono_of_subset hpq hS hS' hSS' φ
      hgS hgS'
      (RieszSigmaFiniteComplete.extByZeroCLM hS hp0 hptop)
      (RieszSigmaFiniteComplete.extByZeroCLM_coeFn hS hp0 hptop)
      (RieszSigmaFiniteComplete.extByZeroCLM hS' hp0 hptop)
      (RieszSigmaFiniteComplete.extByZeroCLM_coeFn hS' hp0 hptop)
      hrepS hrepS'
  · -- Hcons
    intro S S' hS hS' hSS' gS gS' hgS hgS' hrepS hrepS'
    exact RieszLpDualityConsistency.representer_ae_eq_of_subset hpq hS hS' hSS' φ
      hgS hgS'
      (RieszSigmaFiniteComplete.extByZeroCLM hS hp0 hptop)
      (RieszSigmaFiniteComplete.extByZeroCLM_coeFn hS hp0 hptop)
      (RieszSigmaFiniteComplete.extByZeroCLM hS' hp0 hptop)
      (RieszSigmaFiniteComplete.extByZeroCLM_coeFn hS' hp0 hptop)
      hrepS hrepS'
  · -- HsigU
    exact fun S hSm hSσ => RieszLpDualityIngredients.sigmaFinite_restrict_iUnion hSm hSσ
  · -- Hglue
    exact fun hT hU hTU hq0 hqtop hg hle =>
      RieszLpDualityGluing.eLpNorm_ae_zero_on_diff_of_le hT hU hTU hq0 hqtop hg hle

-- Axiom audit (2026-07-08, researcher-4). The headline reduction
-- `riesz_lp_surjective_general` is now DISCHARGED (the maximality `sorry` is gone)
-- and machine-checked with foundational axioms only: a full Docker kernel build
-- reports `depends on axioms: [propext, Classical.choice, Quot.sound]` — no
-- `sorryAx`, no `Lean.ofReduceBool`. The five ingredient lemmas remain
-- foundational-only as before.
#print axioms RieszLpDualitySynthesis.memLp_exists_sigmaFinite_support
#print axioms RieszLpDualitySynthesis.sigmaFinite_restrict_iUnion
#print axioms RieszLpDualitySynthesis.eLpNorm_rpow_restrict_union
#print axioms RieszLpDualitySynthesis.eLpNorm_rpow_restrict_iUnion
#print axioms RieszLpDualitySynthesis.eLpNorm_rpow_restrict_mono
#print axioms RieszLpDualitySynthesis.riesz_representer_on_sigmaFinite_set
#print axioms RieszLpDualitySynthesis.riesz_lp_surjective_general

end RieszLpDualitySynthesis

end
