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

end RieszLpDualityIngredients

end
