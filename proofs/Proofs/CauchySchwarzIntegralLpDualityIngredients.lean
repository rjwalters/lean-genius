/-
# Lᵖ-duality reduction: the Mathlib-only ingredient lemmas
(cauchy-schwarz-integral-lp-duality-synthesis)

This file collects the **measure-theoretic ingredient lemmas** used by the
arbitrary-measure → σ-finite reduction of the Lᵖ Riesz representation theorem
(`CauchySchwarzIntegralLpDualitySynthesis.lean`, Folland *Real Analysis* 2nd ed.,
Thm 6.16). Every lemma here depends on **Mathlib only** — none of them import the
`CauchySchwarz…` Riesz dependency chain — so they are independently
kernel-checkable and are registered in `Proofs.lean` as a regression guard.

Each is a genuine Mathlib gap (confirmed by source search against the pinned
Mathlib v4.26.0): Mathlib provides the σ-finite-support fact, the *binary*-union
σ-finiteness instance, the disjoint additivity of the lower integral, and
unit-exponent `eLpNorm` additivity, but **not** the packaged forms below — the
σ-finiteness of a *countable* restricted union, nor the `q`-power additivity of the
Lᵠ-seminorm over disjoint unions (binary / countable), set differences, and the
resulting monotonicity over set inclusion.

## Contents

* `memLp_exists_sigmaFinite_support` — every `f ∈ Lᵖ`, `0 < p < ∞`, is a.e.
  supported on a measurable set whose restricted measure is σ-finite.
* `sigmaFinite_restrict_iUnion` — σ-finiteness of a restriction is closed under
  countable unions (of measurable sets).
* `eLpNorm_rpow_restrict_union` / `…_iUnion` — `q`-power additivity of the
  Lᵠ-seminorm over a binary / countable disjoint union of measurable sets.
* `eLpNorm_rpow_restrict_diff` — `q`-power additivity over a set difference
  `B = A ⊔ (B \ A)` (the decomposition the maximality *gluing* actually uses).
* `eLpNorm_rpow_restrict_mono` — monotonicity of the `q`-power Lᵠ-seminorm under
  set inclusion `A ⊆ B` (the maximizing sequence's norms increase with the set).

Beyond the σ-finite-reduction ingredients, the file develops the **dual-norm
characterization** that is the analytic core of `Lᵖ`-duality:

* `lintegral_extremizer_*` / `exists_holder_extremizer` — converse Hölder: the
  explicit extremizer `f = g^{q-1}` attains *equality* in Hölder's inequality.
* `lpDualNorm` / `lpDualNorm_le` / `lpDualNorm_eq_of_lintegral_ne_top` — the dual
  norm `⨆_{‖f‖_p ≤ 1} ∫⁻ f·g` equals `‖g‖_q` for `g ∈ Lᵠ`.
* `lqTruncation` + `iSup_lqTruncation` / `lpDualNorm_eq_top_of_lintegral_top` — the
  `g ∉ Lᵠ` direction via monotone truncation over the spanning sets.
* `lpDualNorm_eq` — the **unconditional** dual-norm identity
  `lpDualNorm p g = (∫⁻ gᵠ)^{1/q} = ‖g‖_q` for a σ-finite measure and any
  measurable `g` (no integrability hypothesis).
* `exists_lpDualNorm_eq` — **attainment**: for `g ∈ Lᵠ` the defining supremum is a
  genuine *maximum*, realized by an explicit extremal `f` in the `Lᵖ` unit ball
  (`f = 0` if `‖g‖_q = 0`, else the normalized extremizer). Existence of a norming
  function for the pairing functional `f ↦ ∫⁻ f·g`.
* `eLpNorm_eq_lpDualNorm` — the **reflexive** norming form
  `‖f‖_p = lpDualNorm q f`: the original `Lᵖ`-norm is recovered by testing against
  the `Lᵠ` unit ball (the `p ↔ q` mirror of `lpDualNorm_eq_eLpNorm`).
-/

import Mathlib

noncomputable section

open MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace RieszLpDualityIngredients

/-- **Bridge lemma.** For `0 < p < ∞`, every `f ∈ Lᵖ(μ)` is a.e. supported on a
    measurable set `S` whose restricted measure `μ.restrict S` is σ-finite: `f = 0`
    a.e. on the complement of `S`.

    This is the ingredient that reduces the *arbitrary-measure* Riesz representation
    to the *σ-finite* case. Mathlib supplies it via `MemLp.aefinStronglyMeasurable`. -/
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
    maximality reduction — forming the σ-finite set `T = ⋃ₙ Sₙ` from a maximizing
    sequence `Sₙ`. The measurability hypothesis is harmless for the application: the
    σ-finite supports produced by `AEFinStronglyMeasurable.sigmaFiniteSet` are
    measurable.

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

/-- **Lᵠ-seminorm `q`-power additivity over a disjoint union.**
    For `0 < q < ∞` and disjoint measurable sets `A`, `B`, the `q`-th power of the
    Lᵠ-seminorm is additive over `A ∪ B`:

      `‖g‖_{q, A ∪ B}^q = ‖g‖_{q, A}^q + ‖g‖_{q, B}^q`.

    This is the analytic identity behind the maximality *gluing* in the reduction.
    Mathlib supplies the underlying disjoint additivity of the lower integral
    (`Measure.restrict_union` + `lintegral_add_measure`) and the unit-exponent
    measure-additivity `eLpNorm_one_add_measure`, but **not** this packaged
    `q`-power identity for `eLpNorm` at a general finite exponent (source-searched).
    The `q`-th power is the right invariant: the seminorm itself is only *sub*additive
    (Minkowski, `eLpNorm_add_le`), whereas its `q`-th power splits exactly over
    disjoint supports. -/
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
    (the countable generalization of `eLpNorm_rpow_restrict_union`).
    For `0 < q < ∞` and a pairwise-disjoint, measurable family `Sₙ`:

      `‖g‖_{q, ⋃ₙ Sₙ}^q = ∑ₙ ‖g‖_{q, Sₙ}^q`.

    This is the form step 2 of the maximality reduction consumes: the maximizing set
    `T = ⋃ₙ Sₙ` is a *countable* union. Like its binary companion it is absent from
    Mathlib for a general finite exponent. The proof is the same
    `eLpNorm_eq_lintegral_rpow_enorm` reduction, closed by the σ-additive
    `Measure.restrict_iUnion`/`lintegral_sum_measure` pair. -/
theorem eLpNorm_rpow_restrict_iUnion {g : α → ℝ} {S : ℕ → Set α}
    (hSm : ∀ n, MeasurableSet (S n)) (hSd : Pairwise (Function.onFun Disjoint S))
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqtop : q ≠ ∞) :
    eLpNorm g q (μ.restrict (⋃ n, S n)) ^ q.toReal
      = ∑' n, eLpNorm g q (μ.restrict (S n)) ^ q.toReal := by
  have hqr : q.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hq0, hqtop⟩
  simp only [eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop, ← ENNReal.rpow_mul,
    one_div_mul_cancel hqr, ENNReal.rpow_one]
  rw [Measure.restrict_iUnion hSd hSm, lintegral_sum_measure]

/-- **Lᵠ-seminorm `q`-power additivity over a set difference.**
    For `0 < q < ∞`, measurable `A ⊆ B`:

      `‖g‖_{q, B}^q = ‖g‖_{q, A}^q + ‖g‖_{q, B \ A}^q`.

    This is the decomposition the maximality *gluing* uses directly: with the
    maximizing hull `T ⊆ U`, write `U = T ⊔ (U \ T)`; additivity over the disjoint
    pieces plus the maximality bound `‖g_U‖_q ≤ ‖g_T‖_q` forces the `U \ T`
    contribution to `0`. A specialization of `eLpNorm_rpow_restrict_union` to the
    canonical disjoint decomposition `A ⊔ (B \ A) = B`. -/
theorem eLpNorm_rpow_restrict_diff {g : α → ℝ} {A B : Set α}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqtop : q ≠ ∞) :
    eLpNorm g q (μ.restrict B) ^ q.toReal
      = eLpNorm g q (μ.restrict A) ^ q.toReal
        + eLpNorm g q (μ.restrict (B \ A)) ^ q.toReal := by
  conv_lhs => rw [← Set.union_diff_cancel hAB]
  exact eLpNorm_rpow_restrict_union (hB.diff hA) disjoint_sdiff_self_right hq0 hqtop

/-- **Monotonicity of the `q`-power Lᵠ-seminorm under set inclusion.**
    For `0 < q < ∞`, measurable `A ⊆ B`:

      `‖g‖_{q, A}^q ≤ ‖g‖_{q, B}^q`.

    The maximizing sequence in the reduction grows the set; this records that the
    Lᵠ-mass is monotone in the restricting set (the `B \ A` contribution is `≥ 0`).
    Immediate from `eLpNorm_rpow_restrict_diff`. -/
theorem eLpNorm_rpow_restrict_mono {g : α → ℝ} {A B : Set α}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqtop : q ≠ ∞) :
    eLpNorm g q (μ.restrict A) ^ q.toReal ≤ eLpNorm g q (μ.restrict B) ^ q.toReal := by
  rw [eLpNorm_rpow_restrict_diff hA hB hAB hq0 hqtop]
  exact le_self_add

/-! ## Converse Hölder: the extremizer attaining equality

Mathlib supplies the Hölder *upper* bound `ENNReal.lintegral_mul_le_Lp_mul_Lq`
(`∫⁻ f·g ≤ ‖f‖_p · ‖g‖_q` for Hölder-conjugate `p, q`) but **not** the converse
fact that the bound is *sharp* — that the explicit extremizer `f = g^{q-1}` attains
equality. That sharpness is exactly what upgrades the upper bound to the dual-norm
identity `‖g‖_q = sup_{‖f‖_p ≤ 1} ∫⁻ f·g`, the analytic core of the `Lᵖ`-duality
(Riesz representation) being reduced. We work in the `ℝ≥0∞` setting throughout,
where the lower integral `∫⁻ g^q` *is* `‖g‖_q^q`, sidestepping the real-valued
sign/integrability bookkeeping; the conjugacy arithmetic is `Real.HolderConjugate`.

The two pointwise identities driving everything are
`(q−1)·p = q` (so `(g^{q-1})^p = g^q`) and `(q−1)+1 = q` (so `g^{q-1}·g = g^q`),
which between them make the Hölder right-hand side `(∫⁻ g^q)^{1/p}·(∫⁻ g^q)^{1/q}`
collapse — via `1/p + 1/q = 1` — to `∫⁻ g^q`, the left-hand side. -/

variable {g : α → ℝ≥0∞}

/-- **Extremizer power identity.** For Hölder-conjugate `p, q`, the `p`-th power of
    the extremizer `g^{q-1}` integrates to the `q`-th power lower integral of `g`:

      `∫⁻ ((g)^{q-1})^p = ∫⁻ (g)^q`.

    Pointwise this is `((g x)^{q-1})^p = (g x)^{(q-1)·p} = (g x)^q`, using the
    conjugacy arithmetic `(q-1)·p = q` (`HolderConjugate.sub_one_mul_conj`). This is
    the identity that makes `‖g^{q-1}‖_p = ‖g‖_q^{q-1}` — the normalization of the
    extremizer in the dual-norm computation. -/
theorem lintegral_extremizer_rpow {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∫⁻ x, ((g x) ^ (q - 1)) ^ p ∂μ = ∫⁻ x, (g x) ^ q ∂μ := by
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.rpow_mul, hpq.symm.sub_one_mul_conj]

/-- **Extremizer pairing identity.** For `1 ≤ q`, the extremizer `g^{q-1}` paired
    against `g` integrates to the `q`-th power lower integral of `g`:

      `∫⁻ (g)^{q-1} · g = ∫⁻ (g)^q`.

    Pointwise `(g x)^{q-1} · g x = (g x)^{(q-1)+1} = (g x)^q` via
    `ENNReal.rpow_add_of_nonneg` (the unconditional `ℝ≥0∞` exponent-additivity for
    nonnegative exponents). This is the numerator `∫⁻ f·g` of the dual pairing at the
    extremizer. -/
theorem lintegral_extremizer_mul {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ x, (g x) ^ (q - 1) * g x ∂μ = ∫⁻ x, (g x) ^ q ∂μ := by
  refine lintegral_congr fun x => ?_
  have hqe : q - 1 + 1 = q := by ring
  conv_rhs => rw [← hqe, ENNReal.rpow_add_of_nonneg (q - 1) 1 (by linarith) zero_le_one,
    ENNReal.rpow_one]

/-- **Converse Hölder / sharpness at the extremizer.** For Hölder-conjugate `p, q`
    the explicit extremizer `f = g^{q-1}` attains *equality* in Hölder's inequality:

      `∫⁻ (g)^{q-1} · g = (∫⁻ ((g)^{q-1})^p)^{1/p} · (∫⁻ (g)^q)^{1/q}`.

    Combined with the Mathlib upper bound `ENNReal.lintegral_mul_le_Lp_mul_Lq`, this
    shows the Hölder bound is sharp — the dual norm of `g ↦ ∫⁻ f·g` over the `Lᵖ`
    unit ball equals `‖g‖_q = (∫⁻ g^q)^{1/q}`. Proof: both integrals on the right
    equal `∫⁻ g^q` (the two extremizer identities), and
    `(∫⁻ g^q)^{1/p} · (∫⁻ g^q)^{1/q} = (∫⁻ g^q)^{1/p + 1/q} = (∫⁻ g^q)^1`
    by `1/p + 1/q = 1` (`HolderConjugate.inv_add_inv_eq_one`). The collapse is
    edge-case-free: `ENNReal.rpow_add_of_nonneg` needs only `1/p, 1/q ≥ 0`, so the
    degenerate `∫⁻ g^q ∈ {0, ∞}` cases require no separate handling. -/
theorem lintegral_extremizer_holder_eq {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∫⁻ x, (g x) ^ (q - 1) * g x ∂μ
      = (∫⁻ x, ((g x) ^ (q - 1)) ^ p ∂μ) ^ (1 / p)
        * (∫⁻ x, (g x) ^ q ∂μ) ^ (1 / q) := by
  have hp : (0 : ℝ) < p := lt_trans one_pos hpq.lt
  have hq : (0 : ℝ) < q := lt_trans one_pos hpq.symm.lt
  rw [lintegral_extremizer_mul hpq.symm.lt.le, lintegral_extremizer_rpow hpq,
    ← ENNReal.rpow_add_of_nonneg (1 / p) (1 / q) (one_div_nonneg.2 hp.le)
      (one_div_nonneg.2 hq.le), one_div, one_div, hpq.inv_add_inv_eq_one, ENNReal.rpow_one]

/-- **Hölder is sharp: existence of an attaining extremizer.** Packaged existential
    form of `lintegral_extremizer_holder_eq`: for Hölder-conjugate `p, q` and
    measurable `g`, there is a measurable `f` (namely `g^{q-1}`) attaining equality
    in Hölder's inequality. This is the converse to `lintegral_mul_le_Lp_mul_Lq`: the
    pairing `g ↦ ∫⁻ f·g` realizes the full dual norm `‖g‖_q`, not merely a lower
    bound for it. -/
theorem exists_holder_extremizer {p q : ℝ} (hpq : p.HolderConjugate q)
    (hg : Measurable g) :
    ∃ f : α → ℝ≥0∞, Measurable f ∧
      ∫⁻ x, f x * g x ∂μ
        = (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) * (∫⁻ x, (g x) ^ q ∂μ) ^ (1 / q) :=
  ⟨fun x => (g x) ^ (q - 1), hg.pow_const _, lintegral_extremizer_holder_eq hpq⟩

/-! ## The dual-norm characterization (the analytic core of Lᵖ-duality)

The sharpness layer above upgrades the Hölder *upper* bound to an *identity* for the
dual pairing. Define the `Lᵖ`-dual norm of `g` as the supremum of the pairing
`∫⁻ f·g` over the `Lᵖ` unit ball `{f : ‖f‖_p ≤ 1}`:

  `lpDualNorm p g = ⨆_{f aemeasurable, ∫⁻ fᵖ ≤ 1} ∫⁻ f·g`.

The content of `Lᵖ`-`Lᵠ` duality is that this equals `‖g‖_q = (∫⁻ gᵠ)^{1/q}`. We prove
the full identity for every `g ∈ Lᵠ` (`∫⁻ gᵠ ≠ ∞`):

* `lpDualNorm_le` — the `≤` direction is Hölder
  (`ENNReal.lintegral_mul_le_Lp_mul_Lq`); it holds unconditionally.
* `lpDualNorm_eq_of_lintegral_ne_top` — the `≥` direction is realized by the
  *normalized* extremizer `(∫⁻ gᵠ)^{-1/p}·g^{q-1}`, which lies on the unit sphere
  `‖f‖_p = 1` and pairs to exactly `‖g‖_q`.

Only `∫⁻ gᵠ = ∞` (`g ∉ Lᵠ`) is left open — it needs a separate truncation/exhaustion
argument and is not the regime relevant to the duality. The two scaling lemmas
`lintegral_scaled_extremizer_rpow/_mul` (how the `q`-power norm and the pairing
transform under a constant rescaling `g^{q-1} ↦ c·g^{q-1}`) isolate the only
analytic input beyond the unscaled extremizer identities. -/

/-- **Scaling of the extremizer's `Lᵖ`-mass.** For Hölder-conjugate `p, q` and any
    `c` with `cᵖ ≠ ∞`, the `p`-th power lower integral of the rescaled extremizer
    `c·g^{q-1}` is `cᵖ·∫⁻ gᵠ`. Pulls the constant `cᵖ` out of the lower integral
    (`mul_rpow_of_nonneg` pointwise, then `lintegral_const_mul'`) and reuses the
    unscaled `lintegral_extremizer_rpow`. -/
theorem lintegral_scaled_extremizer_rpow {p q : ℝ} (hpq : p.HolderConjugate q)
    {c : ℝ≥0∞} (hc : c ^ p ≠ ∞) :
    ∫⁻ x, (c * (g x) ^ (q - 1)) ^ p ∂μ = c ^ p * ∫⁻ x, (g x) ^ q ∂μ := by
  have hp : (0 : ℝ) < p := lt_trans one_pos hpq.lt
  rw [← lintegral_extremizer_rpow hpq, ← lintegral_const_mul' _ _ hc]
  exact lintegral_congr fun x => by rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]

/-- **Scaling of the extremizer's pairing with `g`.** For `1 ≤ q` and any finite `c`,
    pairing the rescaled extremizer `c·g^{q-1}` against `g` scales the unscaled pairing
    by `c`: `∫⁻ (c·g^{q-1})·g = c·∫⁻ gᵠ`. Constant pulled out via
    `lintegral_const_mul'`, reusing `lintegral_extremizer_mul`. -/
theorem lintegral_scaled_extremizer_mul {q : ℝ} (hq : 1 ≤ q)
    {c : ℝ≥0∞} (hc : c ≠ ∞) :
    ∫⁻ x, c * (g x) ^ (q - 1) * g x ∂μ = c * ∫⁻ x, (g x) ^ q ∂μ := by
  rw [← lintegral_extremizer_mul hq, ← lintegral_const_mul' _ _ hc]
  exact lintegral_congr fun x => by rw [mul_assoc]

/-- The normalized Hölder extremizer `c·g^{q-1}` with `c = (∫⁻ gᵠ)^{-1/p}`, scaled to
    lie on the `Lᵖ` unit sphere `∫⁻ fᵖ = 1` (for `g ∈ Lᵠ` with `‖g‖_q ≠ 0`). -/
def normalizedExtremizer (p q : ℝ) (μ : Measure α) (g : α → ℝ≥0∞) : α → ℝ≥0∞ :=
  fun x => ((∫⁻ y, (g y) ^ q ∂μ) ^ (1 / p))⁻¹ * (g x) ^ (q - 1)

/-- The normalized extremizer is measurable when `g` is. -/
theorem measurable_normalizedExtremizer {p q : ℝ} (hg : Measurable g) :
    Measurable (normalizedExtremizer p q μ g) :=
  measurable_const.mul (hg.pow_const _)

/-- **The `Lᵖ`-dual norm of `g`**: the supremum of the dual pairing `∫⁻ f·g` over the
    `Lᵖ` unit ball `{f aemeasurable : ∫⁻ fᵖ ≤ 1}`. Duality (below) identifies it with
    the `Lᵠ`-seminorm `(∫⁻ gᵠ)^{1/q}` for `g ∈ Lᵠ`. -/
def lpDualNorm (p : ℝ) (μ : Measure α) (g : α → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (f : α → ℝ≥0∞) (_ : AEMeasurable f μ) (_ : ∫⁻ x, (f x) ^ p ∂μ ≤ 1),
    ∫⁻ x, f x * g x ∂μ

/-- **Dual norm `≤` Lᵠ-seminorm (Hölder, unconditional).** Every admissible `f`
    (`∫⁻ fᵖ ≤ 1`) pairs to at most `(∫⁻ gᵠ)^{1/q}`, by Hölder's inequality with the
    unit-ball normalization `(∫⁻ fᵖ)^{1/p} ≤ 1`. Hence the supremum is `≤ ‖g‖_q`. -/
theorem lpDualNorm_le {p q : ℝ} (hpq : p.HolderConjugate q) (hg : AEMeasurable g μ) :
    lpDualNorm p μ g ≤ (∫⁻ x, (g x) ^ q ∂μ) ^ (1 / q) := by
  have hp : (0 : ℝ) < p := lt_trans one_pos hpq.lt
  refine iSup_le fun f => iSup_le fun hf => iSup_le fun hfp => ?_
  calc ∫⁻ x, f x * g x ∂μ
      ≤ (∫⁻ x, (f x) ^ p ∂μ) ^ (1 / p) * (∫⁻ x, (g x) ^ q ∂μ) ^ (1 / q) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf hg
    _ ≤ (1 : ℝ≥0∞) ^ (1 / p) * (∫⁻ x, (g x) ^ q ∂μ) ^ (1 / q) :=
        mul_le_mul' (ENNReal.rpow_le_rpow hfp (one_div_nonneg.2 hp.le)) le_rfl
    _ = (∫⁻ x, (g x) ^ q ∂μ) ^ (1 / q) := by rw [ENNReal.one_rpow, one_mul]

/-- **Lᵖ-duality dual-norm identity for `g ∈ Lᵠ`.** For Hölder-conjugate `p, q` and
    measurable `g` with `∫⁻ gᵠ ≠ ∞`:

      `lpDualNorm p g = (∫⁻ gᵠ)^{1/q} = ‖g‖_q`.

    The `≤` is `lpDualNorm_le` (Hölder). The `≥` splits on `‖g‖_q`:
    * `∫⁻ gᵠ = 0`: then `‖g‖_q = 0 ≤ lpDualNorm` trivially.
    * `0 < ∫⁻ gᵠ < ∞`: the *normalized* extremizer `(∫⁻ gᵠ)^{-1/p}·g^{q-1}` is
      admissible — its `Lᵖ`-mass is `cᵖ·∫⁻ gᵠ = (∫⁻ gᵠ)⁻¹·∫⁻ gᵠ = 1` — and pairs to
      `c·∫⁻ gᵠ = (∫⁻ gᵠ)^{-1/p}·∫⁻ gᵠ = (∫⁻ gᵠ)^{1/q}` (since `-1/p + 1 = 1/q`),
      realizing the supremum. This is the converse to Hölder: the dual pairing
      attains the full `Lᵠ`-seminorm, not merely a lower bound for it. -/
theorem lpDualNorm_eq_of_lintegral_ne_top {p q : ℝ} (hpq : p.HolderConjugate q)
    (hg : Measurable g) (hItop : (∫⁻ x, (g x) ^ q ∂μ) ≠ ∞) :
    lpDualNorm p μ g = (∫⁻ x, (g x) ^ q ∂μ) ^ (1 / q) := by
  have hp : (0 : ℝ) < p := lt_trans one_pos hpq.lt
  have hq : (0 : ℝ) < q := lt_trans one_pos hpq.symm.lt
  refine le_antisymm (lpDualNorm_le hpq hg.aemeasurable) ?_
  rcases eq_or_ne (∫⁻ x, (g x) ^ q ∂μ) 0 with hI0 | hI0
  · -- ‖g‖_q = 0
    rw [hI0, ENNReal.zero_rpow_of_pos (one_div_pos.2 hq)]
    exact zero_le _
  · -- 0 < ‖g‖_q < ∞ : the normalized extremizer attains the supremum
    set I := ∫⁻ x, (g x) ^ q ∂μ with hIdef
    have hIpos : (0 : ℝ≥0∞) < I := lt_of_le_of_ne (zero_le _) (Ne.symm hI0)
    have hIp0 : I ^ (1 / p) ≠ 0 := (ENNReal.rpow_pos hIpos hItop).ne'
    have hIptop : I ^ (1 / p) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 hp.le) hItop
    have hc_ne_top : ((I ^ (1 / p))⁻¹ : ℝ≥0∞) ≠ ∞ := ENNReal.inv_ne_top.2 hIp0
    have hcp : ((I ^ (1 / p))⁻¹ : ℝ≥0∞) ^ p = I⁻¹ := by
      rw [ENNReal.inv_rpow, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
    have hcp_ne_top : ((I ^ (1 / p))⁻¹ : ℝ≥0∞) ^ p ≠ ∞ := by rw [hcp]; exact ENNReal.inv_ne_top.2 hI0
    -- the normalized extremizer lies on the unit sphere
    have hf_norm : ∫⁻ x, (normalizedExtremizer p q μ g x) ^ p ∂μ = 1 := by
      simp only [normalizedExtremizer, ← hIdef]
      rw [lintegral_scaled_extremizer_rpow hpq hcp_ne_top, ← hIdef, hcp,
        ENNReal.inv_mul_cancel hI0 hItop]
    -- and pairs to exactly ‖g‖_q
    have hexp : -(1 / p) + 1 = 1 / q := by
      have h := hpq.inv_add_inv_eq_one
      simp only [one_div]; linarith
    have hcI : ((I ^ (1 / p))⁻¹ : ℝ≥0∞) * I = I ^ (1 / q) := by
      rw [← hexp, ENNReal.rpow_add _ _ hI0 hItop, ENNReal.rpow_neg, ENNReal.rpow_one]
    have hf_pair : ∫⁻ x, normalizedExtremizer p q μ g x * g x ∂μ = I ^ (1 / q) := by
      simp only [normalizedExtremizer, ← hIdef]
      rw [lintegral_scaled_extremizer_mul hpq.symm.lt.le hc_ne_top, ← hIdef, hcI]
    -- realize the supremum at the normalized extremizer
    rw [← hf_pair]
    exact le_iSup_of_le (normalizedExtremizer p q μ g)
      (le_iSup_of_le (measurable_normalizedExtremizer hg).aemeasurable
        (le_iSup_of_le hf_norm.le (le_refl _)))

/-- **Monotonicity of the dual norm in `g`.** If `g₁ ≤ g₂` pointwise then every dual
    pairing `∫⁻ f·g₁` is dominated by `∫⁻ f·g₂` (same admissible `f`), so the supremum
    is monotone: `lpDualNorm p g₁ ≤ lpDualNorm p g₂`. This is the tool that transports
    the finite-seminorm dual-norm identity to lower truncations of an arbitrary `g`. -/
theorem lpDualNorm_mono {p : ℝ} {g₁ g₂ : α → ℝ≥0∞} (h : ∀ x, g₁ x ≤ g₂ x) :
    lpDualNorm p μ g₁ ≤ lpDualNorm p μ g₂ := by
  refine iSup_le fun f => iSup_le fun hf => iSup_le fun hfp => ?_
  refine le_trans (lintegral_mono fun x => mul_le_mul' (le_refl _) (h x)) ?_
  exact le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hfp (le_refl _)))

/-- **Lower bound on the dual norm from a finite-seminorm truncation.** For any
    measurable `h ≤ g` with `∫⁻ hᵠ ≠ ∞`, the dual norm of `g` is at least the
    Lᵠ-seminorm of `h`:

      `(∫⁻ hᵠ)^{1/q} ≤ lpDualNorm p g`.

    Combine `lpDualNorm_mono` (`h ≤ g`) with the finite-case identity
    `lpDualNorm_eq_of_lintegral_ne_top` applied to `h`. This is the engine for the
    `g ∉ Lᵠ` direction: as `h` ranges over truncations of `g` with `∫⁻ hᵠ ↑ ∫⁻ gᵠ`,
    the right side is forced up to `(∫⁻ gᵠ)^{1/q}`. -/
theorem lpDualNorm_ge_of_le {p q : ℝ} (hpq : p.HolderConjugate q)
    {g h : α → ℝ≥0∞} (hh : Measurable h) (hle : ∀ x, h x ≤ g x)
    (hhtop : (∫⁻ x, (h x) ^ q ∂μ) ≠ ∞) :
    (∫⁻ x, (h x) ^ q ∂μ) ^ (1 / q) ≤ lpDualNorm p μ g := by
  rw [← lpDualNorm_eq_of_lintegral_ne_top hpq hh hhtop]
  exact lpDualNorm_mono hle

/-! ## Completing the dual-norm identity: the `g ∉ Lᵠ` direction (σ-finite `μ`)

The finite-seminorm case (`lpDualNorm_eq_of_lintegral_ne_top`) together with the
truncation bridge (`lpDualNorm_ge_of_le`) close the remaining `∫⁻ gᵠ = ∞`
(`g ∉ Lᵠ`) regime **for a σ-finite measure**. Truncate `g` to
`tₙ = (g ⊓ n) · 1_{Aₙ}` over the finite-measure spanning sets `Aₙ = spanningSets μ n`:
the `tₙ` are measurable, increase pointwise to `g`, and each has finite Lᵠ-mass
(`∫⁻ tₙᵠ ≤ nᵠ · μ(Aₙ) < ∞`). By monotone convergence their masses exhaust
`∫⁻ gᵠ = ∞`, and the bridge turns each finite mass into a lower bound
`(∫⁻ tₙᵠ)^{1/q} ≤ lpDualNorm`; the supremum of the left sides is `∞`. This yields
the **unconditional** dual-norm identity `lpDualNorm p g = ‖g‖_q` (σ-finite `μ`,
*no* integrability hypothesis on `g`) — the full analytic core of `Lᵖ`-duality. -/

/-- A positive real power commutes with suprema on `ℝ≥0∞`: the power map
    `x ↦ x^q` (`q > 0`) is an order isomorphism (`ENNReal.orderIsoRpow`), so it
    preserves `⨆`. -/
private theorem rpow_iSup {ι : Sort*} (f : ι → ℝ≥0∞) {q : ℝ} (hq : 0 < q) :
    (⨆ i, f i) ^ q = ⨆ i, (f i) ^ q := by
  have h := map_iSup (ENNReal.orderIsoRpow q hq) f
  simpa only [ENNReal.orderIsoRpow_apply] using h

/-- The Lᵠ-truncation of `g` to the `n`-th finite-measure spanning set:
    `tₙ = (g ⊓ n) · 1_{spanningSets μ n}`. -/
def lqTruncation (μ : Measure α) [SigmaFinite μ] (g : α → ℝ≥0∞) (n : ℕ) : α → ℝ≥0∞ :=
  (spanningSets μ n).indicator fun y => min (g y) (n : ℝ≥0∞)

/-- The truncation is measurable. -/
theorem measurable_lqTruncation [SigmaFinite μ] (hg : Measurable g) (n : ℕ) :
    Measurable (lqTruncation μ g n) :=
  (hg.min measurable_const).indicator (measurableSet_spanningSets μ n)

/-- The truncation is dominated by `g`. -/
theorem lqTruncation_le [SigmaFinite μ] (n : ℕ) (x : α) :
    lqTruncation μ g n x ≤ g x := by
  by_cases hx : x ∈ spanningSets μ n
  · simp only [lqTruncation, Set.indicator_of_mem hx]; exact min_le_left _ _
  · simp only [lqTruncation, Set.indicator_of_notMem hx]; exact zero_le _

/-- The truncations increase pointwise in `n`. -/
theorem lqTruncation_mono [SigmaFinite μ] {m n : ℕ} (hmn : m ≤ n) (x : α) :
    lqTruncation μ g m x ≤ lqTruncation μ g n x := by
  by_cases hxm : x ∈ spanningSets μ m
  · have hxn : x ∈ spanningSets μ n := monotone_spanningSets μ hmn hxm
    simp only [lqTruncation, Set.indicator_of_mem hxm, Set.indicator_of_mem hxn]
    exact min_le_min le_rfl (by exact_mod_cast hmn)
  · simp only [lqTruncation, Set.indicator_of_notMem hxm]; exact zero_le _

/-- The truncations increase to `g`: `⨆ₙ tₙ = g` pointwise. The `≤` is dominance;
    the `≥` finds a spanning set `Aₖ ∋ x` and exhausts the cap (`g x = ∞`: the cap
    `min ∞ n = n ↑ ∞`; `g x < ∞`: pick `n ≥ g x`, then `min (g x) n = g x`). -/
theorem iSup_lqTruncation [SigmaFinite μ] (x : α) :
    ⨆ n, lqTruncation μ g n x = g x := by
  refine le_antisymm (iSup_le fun n => lqTruncation_le n x) ?_
  have hxU : x ∈ ⋃ n, spanningSets μ n := by rw [iUnion_spanningSets]; exact Set.mem_univ x
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hxU
  rcases eq_or_ne (g x) ∞ with hgx | hgx
  · rw [hgx, top_le_iff, iSup_eq_top]
    intro b hb
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hb.ne
    refine ⟨max k m, ?_⟩
    have hxmem : x ∈ spanningSets μ (max k m) := monotone_spanningSets μ (le_max_left k m) hk
    simp only [lqTruncation, Set.indicator_of_mem hxmem, hgx]
    rw [min_eq_right le_top]
    exact lt_of_lt_of_le hm (by exact_mod_cast Nat.le_max_right k m)
  · obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hgx
    refine le_iSup_of_le (max k m) ?_
    have hxmem : x ∈ spanningSets μ (max k m) := monotone_spanningSets μ (le_max_left k m) hk
    simp only [lqTruncation, Set.indicator_of_mem hxmem]
    exact le_min le_rfl (le_of_lt (lt_of_lt_of_le hm (by exact_mod_cast Nat.le_max_right k m)))

/-- Each truncation has finite Lᵠ-mass: `∫⁻ tₙᵠ ≤ nᵠ · μ(Aₙ) < ∞`. -/
theorem lintegral_lqTruncation_rpow_ne_top [SigmaFinite μ] {q : ℝ} (hq : 0 < q) (n : ℕ) :
    (∫⁻ x, (lqTruncation μ g n x) ^ q ∂μ) ≠ ∞ := by
  have hbound : ∫⁻ x, (lqTruncation μ g n x) ^ q ∂μ
      ≤ (n : ℝ≥0∞) ^ q * μ (spanningSets μ n) := by
    rw [← lintegral_indicator_const (measurableSet_spanningSets μ n)]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ spanningSets μ n
    · rw [Set.indicator_of_mem hx]
      simp only [lqTruncation, Set.indicator_of_mem hx]
      exact ENNReal.rpow_le_rpow (min_le_right _ _) hq.le
    · rw [Set.indicator_of_notMem hx]
      have hz : lqTruncation μ g n x = 0 := by
        simp only [lqTruncation, Set.indicator_of_notMem hx]
      rw [hz]; simp [ENNReal.zero_rpow_of_pos hq]
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le (ENNReal.natCast_ne_top n))
      (measure_spanningSets_lt_top μ n).ne) hbound

/-- **Dual norm is `∞` when `g ∉ Lᵠ` (σ-finite `μ`).** If `∫⁻ gᵠ = ∞` then
    `lpDualNorm p g = ∞ = (∫⁻ gᵠ)^{1/q}`. The truncation masses `∫⁻ tₙᵠ` exhaust
    `∫⁻ gᵠ = ∞` (monotone convergence: `⨆ₙ tₙᵠ = gᵠ`), and each finite mass yields
    `(∫⁻ tₙᵠ)^{1/q} ≤ lpDualNorm` via `lpDualNorm_ge_of_le`; their supremum
    `(⨆ₙ ∫⁻ tₙᵠ)^{1/q} = ∞^{1/q} = ∞` forces the dual norm up to `∞`. -/
theorem lpDualNorm_eq_top_of_lintegral_top [SigmaFinite μ] {p q : ℝ}
    (hpq : p.HolderConjugate q) (hg : Measurable g) (hI : (∫⁻ x, (g x) ^ q ∂μ) = ∞) :
    lpDualNorm p μ g = ∞ := by
  have hq : (0 : ℝ) < q := lt_trans one_pos hpq.symm.lt
  have hmeas : ∀ n, Measurable (fun x => (lqTruncation μ g n x) ^ q) :=
    fun n => (measurable_lqTruncation hg n).pow_const q
  have hmono : Monotone (fun n => fun x => (lqTruncation μ g n x) ^ q) := by
    intro m n hmn x
    exact ENNReal.rpow_le_rpow (lqTruncation_mono hmn x) hq.le
  -- monotone convergence: truncation masses exhaust ∫⁻ gᵠ = ∞
  have hmass : ⨆ n, ∫⁻ x, (lqTruncation μ g n x) ^ q ∂μ = ∞ := by
    rw [← lintegral_iSup hmeas hmono, ← hI]
    refine lintegral_congr fun x => ?_
    rw [← rpow_iSup _ hq, iSup_lqTruncation x]
  -- sup of the truncation lower bounds is ∞
  refine le_antisymm le_top ?_
  calc (∞ : ℝ≥0∞)
      = (⨆ n, ∫⁻ x, (lqTruncation μ g n x) ^ q ∂μ) ^ (1 / q) := by
        rw [hmass, ENNReal.top_rpow_of_pos (one_div_pos.2 hq)]
    _ = ⨆ n, (∫⁻ x, (lqTruncation μ g n x) ^ q ∂μ) ^ (1 / q) := rpow_iSup _ (one_div_pos.2 hq)
    _ ≤ lpDualNorm p μ g :=
        iSup_le fun n => lpDualNorm_ge_of_le hpq (measurable_lqTruncation hg n)
          (lqTruncation_le n) (lintegral_lqTruncation_rpow_ne_top hq n)

/-- **The `Lᵖ`-duality dual-norm identity (σ-finite `μ`, unconditional).** For
    Hölder-conjugate `p, q`, a σ-finite measure `μ`, and any measurable `g`:

      `lpDualNorm p g = (∫⁻ gᵠ)^{1/q} = ‖g‖_q`,

    with *no* integrability hypothesis on `g`. This is the capstone of the
    reduction: the dual norm of the pairing functional `g ↦ ∫⁻ f·g` over the `Lᵖ`
    unit ball is exactly the `Lᵠ`-seminorm — the analytic heart of the `Lᵖ` Riesz
    representation theorem. Combines the finite case
    (`lpDualNorm_eq_of_lintegral_ne_top`) with the `g ∉ Lᵠ` case
    (`lpDualNorm_eq_top_of_lintegral_top`). -/
theorem lpDualNorm_eq [SigmaFinite μ] {p q : ℝ} (hpq : p.HolderConjugate q)
    (hg : Measurable g) :
    lpDualNorm p μ g = (∫⁻ x, (g x) ^ q ∂μ) ^ (1 / q) := by
  rcases eq_or_ne (∫⁻ x, (g x) ^ q ∂μ) ∞ with hI | hI
  · have hq : (0 : ℝ) < q := lt_trans one_pos hpq.symm.lt
    rw [lpDualNorm_eq_top_of_lintegral_top hpq hg hI, hI,
      ENNReal.top_rpow_of_pos (one_div_pos.2 hq)]
  · exact lpDualNorm_eq_of_lintegral_ne_top hpq hg hI

/-- **`eLpNorm` of an `ℝ≥0∞`-valued function as an explicit `rpow` lower integral.**
    For `0 < q` and any `g : α → ℝ≥0∞`, Mathlib's canonical `Lᵠ`-seminorm is the
    bespoke quantity used throughout the dual-norm development:

      `eLpNorm g (ENNReal.ofReal q) μ = (∫⁻ gᵠ)^{1/q}`.

    The enorm of an `ℝ≥0∞` is itself (`enorm_eq_self`) and
    `(ENNReal.ofReal q).toReal = q` for `q ≥ 0`, so the general
    `eLpNorm_eq_lintegral_rpow_enorm` collapses to exactly the form appearing in
    `lpDualNorm_eq`. -/
theorem eLpNorm_ofReal_eq_lintegral_rpow {q : ℝ} (hq : 0 < q) :
    eLpNorm g (ENNReal.ofReal q) μ = (∫⁻ x, (g x) ^ q ∂μ) ^ (1 / q) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_pos.mpr hq).ne'
        ENNReal.ofReal_ne_top]
  simp only [enorm_eq_self, ENNReal.toReal_ofReal hq.le]

/-- **The `Lᵖ`-duality identity in Mathlib's `eLpNorm` vocabulary (σ-finite `μ`).**
    For Hölder-conjugate `p, q`, a σ-finite measure `μ`, and any measurable
    `g : α → ℝ≥0∞`, the dual norm of the pairing functional `f ↦ ∫⁻ f·g` over the
    `Lᵖ` unit ball equals the genuine `Lᵠ`-seminorm of `g`:

      `lpDualNorm p g = eLpNorm g (ENNReal.ofReal q) μ = ‖g‖_q`.

    This is the literal form of "the dual of `Lᵖ` is `Lᵠ`", phrased in Mathlib's own
    `Lᵖ`-space API rather than the ad-hoc `(∫⁻ gᵠ)^{1/q}`. Combines the unconditional
    `lpDualNorm_eq` with the `eLpNorm` bridge `eLpNorm_ofReal_eq_lintegral_rpow`. -/
theorem lpDualNorm_eq_eLpNorm [SigmaFinite μ] {p q : ℝ} (hpq : p.HolderConjugate q)
    (hg : Measurable g) :
    lpDualNorm p μ g = eLpNorm g (ENNReal.ofReal q) μ := by
  have hq : (0 : ℝ) < q := lt_trans one_pos hpq.symm.lt
  rw [lpDualNorm_eq hpq hg, eLpNorm_ofReal_eq_lintegral_rpow hq]

/-- **Finiteness of the dual norm characterizes `Lᵠ`-membership (σ-finite `μ`).** For
    Hölder-conjugate `p, q`, a σ-finite measure, and measurable `g : α → ℝ≥0∞`:

      `g ∈ Lᵠ ↔ lpDualNorm p g < ∞`.

    Immediate from `lpDualNorm_eq_eLpNorm`: `MemLp` is `AEStronglyMeasurable ∧
    eLpNorm < ∞`, and a measurable `ℝ≥0∞`-valued function is automatically
    a.e.-strongly-measurable, so the only content is the finiteness of `eLpNorm`,
    which the dual norm equals. The pairing functional is `Lᵖ`-bounded exactly when
    `g` lies in the conjugate space — the boundedness half of `Lᵖ`-`Lᵠ` duality. -/
theorem memLp_ofReal_iff_lpDualNorm_lt_top [SigmaFinite μ] {p q : ℝ}
    (hpq : p.HolderConjugate q) (hg : Measurable g) :
    MemLp g (ENNReal.ofReal q) μ ↔ lpDualNorm p μ g < ∞ := by
  rw [lpDualNorm_eq_eLpNorm hpq hg]
  exact ⟨fun h => h.2, fun h => ⟨hg.aestronglyMeasurable, h⟩⟩

/-! ## Attainment: the dual norm is a genuine maximum (`g ∈ Lᵠ`)

`lpDualNorm` is defined as a supremum over the `Lᵖ` unit ball. The dual-norm
identity `lpDualNorm_eq_of_lintegral_ne_top` shows the supremum *value* equals
`‖g‖_q`, but the standard "converse Hölder" statement is stronger: for
`g ∈ Lᵠ` the supremum is **attained** by an explicit extremal function — the
supremum is a maximum. The witness is the normalized extremizer
`(∫⁻ gᵠ)^{-1/p}·g^{q-1}` (when `‖g‖_q ≠ 0`) or the zero function (when
`‖g‖_q = 0`, where `g = 0` a.e. and every pairing vanishes). This is exactly the
existence of a *norming function* for the pairing functional `f ↦ ∫⁻ f·g`. -/

/-- **The `Lᵖ`-dual norm is attained for `g ∈ Lᵠ` (converse Hölder, existence
    form).** For Hölder-conjugate `p, q` and measurable `g` with `∫⁻ gᵠ ≠ ∞`,
    there is an admissible `f` (`∫⁻ fᵖ ≤ 1`) whose pairing against `g` realizes
    the dual norm exactly:

      `∃ f, ‖f‖_p ≤ 1  ∧  ∫⁻ f·g = lpDualNorm p g  (= ‖g‖_q)`.

    So the defining supremum is a genuine *maximum*: the pairing functional
    `f ↦ ∫⁻ f·g` is normed by an explicit extremal element of the unit ball. When
    `‖g‖_q = 0` the witness is `f = 0`; otherwise it is the normalized extremizer
    `(∫⁻ gᵠ)^{-1/p}·g^{q-1}`, which lies on the unit sphere and pairs to `‖g‖_q`. -/
theorem exists_lpDualNorm_eq {p q : ℝ} (hpq : p.HolderConjugate q)
    (hg : Measurable g) (hItop : (∫⁻ x, (g x) ^ q ∂μ) ≠ ∞) :
    ∃ f : α → ℝ≥0∞, AEMeasurable f μ ∧ (∫⁻ x, (f x) ^ p ∂μ) ≤ 1 ∧
      ∫⁻ x, f x * g x ∂μ = lpDualNorm p μ g := by
  have hp : (0 : ℝ) < p := lt_trans one_pos hpq.lt
  have hq : (0 : ℝ) < q := lt_trans one_pos hpq.symm.lt
  rw [lpDualNorm_eq_of_lintegral_ne_top hpq hg hItop]
  set I := ∫⁻ x, (g x) ^ q ∂μ with hIdef
  rcases eq_or_ne I 0 with hI0 | hI0
  · -- ‖g‖_q = 0 (`g = 0` a.e.): the zero function attains the value `0 = I^{1/q}`
    refine ⟨0, aemeasurable_const, ?_, ?_⟩
    · simp [ENNReal.zero_rpow_of_pos hp]
    · rw [hI0, ENNReal.zero_rpow_of_pos (one_div_pos.2 hq)]
      simp
  · -- 0 < ‖g‖_q < ∞: the normalized extremizer lies on the unit sphere and
    -- pairs to exactly `I^{1/q}`, realizing the supremum
    have hIpos : (0 : ℝ≥0∞) < I := lt_of_le_of_ne (zero_le _) (Ne.symm hI0)
    have hIp0 : I ^ (1 / p) ≠ 0 := (ENNReal.rpow_pos hIpos hItop).ne'
    have hc_ne_top : ((I ^ (1 / p))⁻¹ : ℝ≥0∞) ≠ ∞ := ENNReal.inv_ne_top.2 hIp0
    have hcp : ((I ^ (1 / p))⁻¹ : ℝ≥0∞) ^ p = I⁻¹ := by
      rw [ENNReal.inv_rpow, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
    have hcp_ne_top : ((I ^ (1 / p))⁻¹ : ℝ≥0∞) ^ p ≠ ∞ := by
      rw [hcp]; exact ENNReal.inv_ne_top.2 hI0
    have hf_norm : ∫⁻ x, (normalizedExtremizer p q μ g x) ^ p ∂μ = 1 := by
      simp only [normalizedExtremizer, ← hIdef]
      rw [lintegral_scaled_extremizer_rpow hpq hcp_ne_top, ← hIdef, hcp,
        ENNReal.inv_mul_cancel hI0 hItop]
    have hexp : -(1 / p) + 1 = 1 / q := by
      have h := hpq.inv_add_inv_eq_one
      simp only [one_div]; linarith
    have hcI : ((I ^ (1 / p))⁻¹ : ℝ≥0∞) * I = I ^ (1 / q) := by
      rw [← hexp, ENNReal.rpow_add _ _ hI0 hItop, ENNReal.rpow_neg, ENNReal.rpow_one]
    have hf_pair : ∫⁻ x, normalizedExtremizer p q μ g x * g x ∂μ = I ^ (1 / q) := by
      simp only [normalizedExtremizer, ← hIdef]
      rw [lintegral_scaled_extremizer_mul hpq.symm.lt.le hc_ne_top, ← hIdef, hcI]
    exact ⟨normalizedExtremizer p q μ g, (measurable_normalizedExtremizer hg).aemeasurable,
      hf_norm.le, hf_pair⟩

/-- **Reflexive norming form of `Lᵖ`-duality (σ-finite `μ`).** For Hölder-conjugate
    `p, q`, a σ-finite measure `μ`, and measurable `f`, the genuine `Lᵖ`-seminorm of
    `f` is recovered as the dual norm of `f` over the `Lᵠ` unit ball:

      `‖f‖_p = eLpNorm f (ENNReal.ofReal p) μ = lpDualNorm q μ f = ⨆_{‖h‖_q ≤ 1} ∫⁻ h·f`.

    This is the symmetric ("double duality" / reflexivity) companion of
    `lpDualNorm_eq_eLpNorm`: not only is the dual of `Lᵖ` the space `Lᵠ`, but the
    original norm is itself recovered by testing against the dual ball. It is the
    `p ↔ q` mirror image, obtained by feeding the conjugacy the other way round
    (`hpq.symm`). -/
theorem eLpNorm_eq_lpDualNorm [SigmaFinite μ] {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    eLpNorm f (ENNReal.ofReal p) μ = lpDualNorm q μ f :=
  (lpDualNorm_eq_eLpNorm hpq.symm hf).symm

end RieszLpDualityIngredients

end
