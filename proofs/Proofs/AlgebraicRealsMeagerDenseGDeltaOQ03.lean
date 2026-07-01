import Mathlib.NumberTheory.Transcendental.Liouville.Residual
import Mathlib.NumberTheory.Transcendental.Liouville.Measure
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic
import Proofs.AlgebraicRealsMeagerDenseGDelta

/-!
# Generically Liouville: a Comeagre Refinement Inside the Transcendental Gδ

## Open Question (algebraic-reals-meager-dense-gdelta-oq-03)

The parent entry `algebraic-reals-meager-dense-gdelta` exhibits the transcendental reals
`{x : ℝ | ¬ IsAlgebraic ℚ x}` as an explicit **dense Gδ** — the residual (comeagre) witness for
the transcendentals. This open question asks to *refine* that picture: the transcendentals are
comeagre, but they are not homogeneous, and one may ask **which** transcendentals are
topologically generic.

The answer is the classical Baire-category theorem for Liouville numbers, here assembled from
Mathlib's `IsGδ.setOf_liouville` / `eventually_residual_liouville` and connected to the parent's
transcendental Gδ. The **Liouville numbers** `{x : ℝ | Liouville x}` are themselves a dense Gδ,
they sit *inside* the transcendentals (`Liouville.transcendental`), and — being comeagre — they
are the topologically generic transcendentals: the transcendentals that are **not** Liouville form
a *meagre* set. So a "generic" transcendental (in the Baire sense) is not merely transcendental but
Liouville.

The striking counterpoint is measure-theoretic. The very same Liouville set has **Lebesgue measure
zero** (`volume_setOf_liouville`). Thus the set of Liouville numbers is simultaneously
**comeagre** (topologically enormous) and **null** (measure-theoretically negligible), and the two
notions of "generic transcendental" diverge completely:

* the **comeagre** transcendental is Liouville (Baire genericity);
* the **almost-every** transcendental is *non*-Liouville (measure genericity).

These two genericity filters are literally disjoint (`Real.disjoint_residual_ae`).

## Main Results

* `liouville_subset_transcendental`: every Liouville number is transcendental over `ℚ` — the
  bridge from Mathlib's `Transcendental ℤ` phrasing to the parent's `¬ IsAlgebraic ℚ` set, via
  denominator clearing (`IsFractionRing.isAlgebraic_iff`).
* `liouville_dense_isGδ`: the Liouville numbers are a dense Gδ in `ℝ`.
* `liouville_residual`: the Liouville numbers are a residual (comeagre) set.
* `transcendental_not_liouville_isMeagre`: **the refinement** — the non-Liouville transcendentals
  are meagre, i.e. the generic transcendental is Liouville.
* `eventually_residual_transcendental_liouville`: comeagrely, a real is transcendental *and*
  Liouville.
* `ae_transcendental_not_liouville`: almost everywhere, a real is transcendental and *not*
  Liouville.
* `liouville_comeagre_yet_null`: **the punchline** — the Liouville set is residual yet Lebesgue-null.
* `generic_transcendental_dichotomy`: the Baire-vs-measure split of the generic transcendental.
-/

open Set Topology MeasureTheory Filter

namespace AlgebraicRealsMeagerDenseGDeltaOQ03

/-! ### The transcendence bridge: Liouville ⟹ transcendental over ℚ -/

/-- **Every Liouville number is transcendental over `ℚ`.**

Mathlib's `Liouville.transcendental` proves transcendence over `ℤ`. Over the *field* `ℚ` this is
the (a priori stronger) statement that no rational-coefficient polynomial annihilates `x`; it
follows by clearing denominators, packaged as `IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ`
(`IsAlgebraic ℤ x ↔ IsAlgebraic ℚ x`). This lands the Liouville set inside the parent's
transcendental Gδ `{x | ¬ IsAlgebraic ℚ x}`. -/
theorem liouville_subset_transcendental :
    {x : ℝ | Liouville x} ⊆ {x : ℝ | ¬ IsAlgebraic ℚ x} := by
  intro x hx halg
  exact hx.transcendental ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr halg)

/-! ### The Liouville numbers are a dense Gδ / residual set -/

/-- **The Liouville numbers are a Gδ in `ℝ`** (Mathlib: `IsGδ.setOf_liouville`). -/
theorem liouville_isGδ : IsGδ {x : ℝ | Liouville x} := IsGδ.setOf_liouville

/-- **The Liouville numbers are a dense Gδ in `ℝ`.** -/
theorem liouville_dense_isGδ :
    IsGδ {x : ℝ | Liouville x} ∧ Dense {x : ℝ | Liouville x} :=
  ⟨IsGδ.setOf_liouville, dense_liouville⟩

/-- **The Liouville numbers are a residual (comeagre) set** (Mathlib:
`eventually_residual_liouville`). -/
theorem liouville_residual : {x : ℝ | Liouville x} ∈ residual ℝ :=
  eventually_residual_liouville

/-! ### The refinement: the generic transcendental is Liouville -/

/-- **The non-Liouville transcendentals are meagre.**

`{x | ¬ IsAlgebraic ℚ x ∧ ¬ Liouville x} ⊆ {x | ¬ Liouville x} = {x | Liouville x}ᶜ`, and the
latter is meagre because the Liouville set is residual. Hence, *generically* (in the Baire sense),
a transcendental real is Liouville. -/
theorem transcendental_not_liouville_isMeagre :
    IsMeagre {x : ℝ | ¬ IsAlgebraic ℚ x ∧ ¬ Liouville x} := by
  have hmeagre : IsMeagre {x : ℝ | ¬ Liouville x} := by
    have hcompl : {x : ℝ | ¬ Liouville x}ᶜ = {x : ℝ | Liouville x} := by
      ext x; simp only [mem_compl_iff, mem_setOf_eq, not_not]
    show {x : ℝ | ¬ Liouville x}ᶜ ∈ residual ℝ
    rw [hcompl]; exact liouville_residual
  exact hmeagre.mono (fun x hx => hx.2)

/-- **Comeagrely, a real is transcendental and Liouville.**

Since the Liouville set is residual and every Liouville number is transcendental over `ℚ`, the
comeagre-many reals are transcendental *and* Liouville. -/
theorem eventually_residual_transcendental_liouville :
    ∀ᶠ x in residual ℝ, ¬ IsAlgebraic ℚ x ∧ Liouville x :=
  eventually_residual_liouville.mono fun _ hx => ⟨liouville_subset_transcendental hx, hx⟩

/-! ### The measure-theoretic counterpoint -/

/-- **Almost every real is transcendental and non-Liouville.**

The algebraic reals are countable (`AlgebraicNumbersCountable.algebraic_reals_countable`), hence
Lebesgue-null, so almost every real is transcendental; and `ae_not_liouville` says almost every
real is non-Liouville. -/
theorem ae_transcendental_not_liouville :
    ∀ᵐ x : ℝ, ¬ IsAlgebraic ℚ x ∧ ¬ Liouville x := by
  have hae_trans : ∀ᵐ x : ℝ, ¬ IsAlgebraic ℚ x := by
    rw [ae_iff]
    simpa using
      (AlgebraicNumbersCountable.algebraic_reals_countable.measure_zero volume)
  exact hae_trans.and ae_not_liouville

/-- **The Liouville set is comeagre yet Lebesgue-null.**

`{x | Liouville x}` is residual (topologically generic) but has Lebesgue measure zero — a set that
is enormous for Baire category and negligible for measure. This is the source of the divergence
between the two notions of "generic transcendental". -/
theorem liouville_comeagre_yet_null :
    {x : ℝ | Liouville x} ∈ residual ℝ ∧ volume {x : ℝ | Liouville x} = 0 :=
  ⟨liouville_residual, volume_setOf_liouville⟩

/-- **The Baire-vs-measure dichotomy of the generic transcendental.**

The topologically generic (comeagre) transcendental is Liouville; the measure-generic
(almost-every) transcendental is *non*-Liouville. The two witnessing filters are disjoint
(`Real.disjoint_residual_ae`), so no single "genericity" reconciles them. -/
theorem generic_transcendental_dichotomy :
    (∀ᶠ x in residual ℝ, ¬ IsAlgebraic ℚ x ∧ Liouville x) ∧
      (∀ᵐ x : ℝ, ¬ IsAlgebraic ℚ x ∧ ¬ Liouville x) :=
  ⟨eventually_residual_transcendental_liouville, ae_transcendental_not_liouville⟩

end AlgebraicRealsMeagerDenseGDeltaOQ03

#print axioms AlgebraicRealsMeagerDenseGDeltaOQ03.liouville_subset_transcendental
#print axioms AlgebraicRealsMeagerDenseGDeltaOQ03.liouville_dense_isGδ
#print axioms AlgebraicRealsMeagerDenseGDeltaOQ03.transcendental_not_liouville_isMeagre
#print axioms AlgebraicRealsMeagerDenseGDeltaOQ03.eventually_residual_transcendental_liouville
#print axioms AlgebraicRealsMeagerDenseGDeltaOQ03.ae_transcendental_not_liouville
#print axioms AlgebraicRealsMeagerDenseGDeltaOQ03.liouville_comeagre_yet_null
#print axioms AlgebraicRealsMeagerDenseGDeltaOQ03.generic_transcendental_dichotomy
