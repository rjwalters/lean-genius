/-
# Lovász Local Lemma — OQ-01: Measure-Theoretic Formulation (base case)

The gallery proof `LovaszLocalLemma.lean` develops the *symmetric* Lovász Local
Lemma entirely over `ℚ` as a combinatorial/probabilistic-budget surrogate: it
never touches a real probability space. Open question OQ-01 asks for the genuine
**measure-theoretic** LLL — events as measurable sets `Aᵢ ⊆ Ω` in a real
`IsProbabilityMeasure`, with the conclusion `μ (⋂ᵢ Aᵢᶜ) > 0` (all bad events can
be simultaneously avoided with positive probability).

The full LLL (bounded dependency degree `d`, budget `e·p·(d+1) ≤ 1`) is a
multi-session research target with no Mathlib counterpart. This file lands the
**`d = 0` base case** — the *mutually independent* regime — as a fully verified,
axiom-free, gap-free measure-theoretic theorem. Every LLL induction bottoms out here,
so this is the honest measure-theoretic anchor for the OQ-01 program.

## Main results

* `lll_independent_meas_iInter_compl` : for mutually independent measurable events
  the avoidance probability factors exactly,
  `μ (⋂ i, (A i)ᶜ) = ∏ i, (1 - μ (A i))`.
* `lll_independent_avoidance` : if additionally every event is *strictly* improbable
  (`μ (A i) < 1`), the avoidance probability is strictly positive,
  `0 < μ (⋂ i, (A i)ᶜ)`. This is the `d = 0` symmetric LLL over a real measure space.

All statements live over an arbitrary `Fintype` index; `IsProbabilityMeasure` is
derived from mutual independence, not assumed.
-/
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace LovaszLocalLemmaOQ01

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
variable {μ : Measure Ω} {A : ι → Set Ω}

/-- Complements of a family remain measurable in the σ-algebra each event generates.
This is the bridge that lets `iIndep.meas_iInter` (which is stated for arbitrary
measurable sets of the independent σ-algebras) apply to the complements `(A i)ᶜ`. -/
theorem compl_measurable_generateFrom (i : ι) :
    MeasurableSet[MeasurableSpace.generateFrom {A i}] (A i)ᶜ :=
  (measurableSet_generateFrom (Set.mem_singleton _)).compl

/-- **Exact avoidance factorization (base case of the LLL).**
For a mutually independent family of measurable events, the probability that *none*
of them occurs equals the product of the individual survival probabilities
`1 - μ (A i)`. This is the `d = 0` (fully independent) instance of the symmetric
Lovász Local Lemma, now over a genuine probability space. -/
theorem lll_independent_meas_iInter_compl
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ) :
    μ (⋂ i, (A i)ᶜ) = ∏ i, (1 - μ (A i)) := by
  haveI : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  -- independence of events ⇒ independence of the σ-algebras they generate
  have hiIndep : iIndep (fun i ↦ MeasurableSpace.generateFrom {A i}) μ :=
    (iIndepSet_iff_iIndep A μ).1 hind
  -- the complements are measurable in those σ-algebras, so the intersection factors
  have hfac : μ (⋂ i, (A i)ᶜ) = ∏ i, μ (A i)ᶜ :=
    hiIndep.meas_iInter (fun i ↦ compl_measurable_generateFrom i)
  rw [hfac]
  refine Finset.prod_congr rfl (fun i _ ↦ ?_)
  rw [prob_compl_eq_one_sub (hA i)]

/-- **Positive avoidance (base case of the LLL).**
If a mutually independent family of measurable events is strictly improbable
(`μ (A i) < 1` for every `i`), then all of them can be avoided simultaneously with
strictly positive probability. This is the measure-theoretic `d = 0` symmetric LLL:
every LLL induction reduces to exactly this independent base case. -/
theorem lll_independent_avoidance
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (hlt : ∀ i, μ (A i) < 1) :
    0 < μ (⋂ i, (A i)ᶜ) := by
  rw [lll_independent_meas_iInter_compl hA hind, zero_lt_iff, Finset.prod_ne_zero_iff]
  intro i _
  exact (tsub_pos_iff_lt.2 (hlt i)).ne'

/-- Reformulation over the uniform bound `μ (A i) ≤ p < 1`: the same strict-avoidance
conclusion holds under a single symmetric probability bound, matching the shape of the
symmetric LLL hypothesis in the rational gallery proof. -/
theorem lll_independent_avoidance_symmetric
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    {p : ℝ≥0∞} (hp : p < 1) (hbound : ∀ i, μ (A i) ≤ p) :
    0 < μ (⋂ i, (A i)ᶜ) :=
  lll_independent_avoidance hA hind (fun i ↦ lt_of_le_of_lt (hbound i) hp)

end LovaszLocalLemmaOQ01
