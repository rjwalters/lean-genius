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

WORK IN PROGRESS. Four ingredient lemmas are now source-complete and self-contained:
the bridge lemma `memLp_exists_sigmaFinite_support` (σ-finite support of an Lᵖ
function), `sigmaFinite_restrict_iUnion` (step 2: countable-union σ-finiteness, a
genuine Mathlib gap, proved here from `Measure.sigmaFinite_of_countable`),
`eLpNorm_rpow_restrict_union` (step 3: `q`-power Lᵠ-seminorm additivity over a
disjoint union, the analytic identity driving the maximality gluing, also absent from
Mathlib for a general finite exponent), and `eLpNorm_restrict_eq_zero_of_le_restrict_left`
(step 3's a.e.-identification *mechanism*: from the maximality bound and that additivity
identity, the representing function is forced to vanish a.e. off the maximal set). The
headline reduction `riesz_lp_surjective_general` still carries a single `sorry` for the
remaining maximality *plumbing* (step 1's `extByZeroCLM` pullback, choosing a maximizing
sequence, and invoking these now-factored analytic facts) — it does **not** yet
eliminate the axiom.

NOT BUILD-VERIFIED: the local Docker build wrapper has been hanging and Aristotle is
unavailable, so `sigmaFinite_restrict_iUnion` is source-complete but its proof has not
been kernel-checked locally; the deployer build-gate is the verifier. Do not present
this file as verified until the `sorry` is discharged and the file builds.

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

/-- **Riesz representation for Lᵖ — arbitrary measure** (`1 < p < ∞`).

    Every bounded linear functional on `Lp ℝ p μ`, for *any* measure `μ`, is
    represented by integration against some `g ∈ Lq(μ)`.

    This is the statement of the parent file's `riesz_lp_surjective` axiom, here
    presented as a theorem to be discharged from `riesz_lp_surjective_sigma_finite`
    via the maximality argument documented at the top of this file.

    REMAINING WORK: the `sorry` below is the maximality construction
    (`riesz_representing_function_maximal`). It is HARD (classical, Folland 6.16),
    not OPEN. Its analytic core is now factored out and source-complete above:
    step 2's σ-finiteness of the maximizing union `T = ⋃ₙ Sₙ`
    (`sigmaFinite_restrict_iUnion`), step 3's `q`-power norm additivity over the
    disjoint gluing pieces `T` and `U \ T` (`eLpNorm_rpow_restrict_union`), and the
    a.e.-identification mechanism that turns the maximality bound into vanishing off
    `T` (`eLpNorm_restrict_eq_zero_of_le_restrict_left`). What remains is the *plumbing*
    that strings them together: pulling `φ` back along `extByZeroCLM` per σ-finite set
    to invoke the σ-finite Riesz theorem, choosing a maximizing sequence, and extracting
    `g_T` — after which `g_U = g_T` a.e. follows from the now-available factored lemmas. -/
theorem riesz_lp_surjective_general
    (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal) [Fact (1 ≤ p)] :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, MemLp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ := by
  sorry

end RieszLpDualitySynthesis

end
