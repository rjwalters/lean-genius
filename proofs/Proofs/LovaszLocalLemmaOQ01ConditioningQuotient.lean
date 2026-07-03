/-
# Lovász Local Lemma — OQ-01: Conditioning-Quotient Bound (the induction step engine)

`Proofs/LovaszLocalLemmaOQ01ChainRule.lean` and
`Proofs/LovaszLocalLemmaOQ01Quantitative.lean` reduce the measure-theoretic LLL to
a single per-event obligation: bound each conditional *failure* probability
`μ[Aₖ | ⋂_{j<k} Aⱼᶜ]` below `1` (they then deliver global avoidance positivity and
the quantitative lower bound `∏ (1 - bₖ) ≤ μ (⋂ Aᵢᶜ)`). Those files never touch the
dependency structure — they are pure telescoping identities.

This file lands the **arithmetic engine of the actual LLL induction**: the step that
bounds a single conditional failure probability by splitting its conditioning
history into two parts. In Spencer's proof of the Lovász Local Lemma one writes the
survival history `H = C ∩ B`, where `C` collects the survivals of the *neighbours*
of the current event and `B` collects the survivals of the *non-neighbours*, and
estimates

  `μ[A | C ∩ B]  ≤  μ[A | B] / μ[C | B]`.

The numerator `μ[A | B]` is later collapsed to `μ A` by independence of `A` from the
non-neighbour survivals `B`; the denominator `μ[C | B]` is bounded below by the
induction hypothesis (`≥ ∏_{neighbours}(1 - xⱼ)`). Together they give
`μ[A | H] ≤ μ A / ∏(1 - xⱼ) ≤ xₐ`, the per-event bound the chain-rule scaffold
consumes.

The bound proved here is **completely general**: no independence, no dependency
graph, no LLL hypothesis — it is a pure conditional-probability inequality over an
arbitrary probability measure, valid for *any* measurable `A`, `B`, `C` with
`μ (C ∩ B) ≠ 0`. It is the honest measure-theoretic core of the LLL inductive step,
the piece that sits between the chain-rule reduction (already formalised) and the
independence/graph input (still open).

## Main results

* `cond_inter_mul_cond_le` : the division-free core
  `μ[A | C ∩ B] · μ[C | B] ≤ μ[A | B]`. Both sides multiply out to a monotonicity
  of measures `μ (C ∩ B ∩ A) ≤ μ (B ∩ A)` after cancelling `μ B`; no independence.
* `cond_inter_le_div` : the quotient form `μ[A | C ∩ B] ≤ μ[A | B] / μ[C | B]`,
  the shape Spencer's LLL proof uses directly.
* `cond_inter_le_of_num_den` : the LLL induction-step conclusion — from a numerator
  bound `μ[A | B] ≤ t` (independence input) and a denominator lower bound
  `q ≤ μ[C | B]` (induction hypothesis) it delivers `μ[A | C ∩ B] ≤ t / q`.
* `cond_inter_lt_one_of_num_den` : the specialisation that produces exactly the
  hypothesis the chain-rule scaffold needs, `μ[A | C ∩ B] < 1`, whenever the
  numerator/denominator ratio `t / q < 1`.

Everything lives over an arbitrary `IsProbabilityMeasure`; no independence
hypothesis is used anywhere.
-/
import Mathlib.Probability.ConditionalProbability

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LovaszLocalLemmaOQ01ConditioningQuotient

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {A B C : Set Ω}

/-- **Conditioning-quotient core (division-free).**
For any measurable `B`, `C` with `μ (C ∩ B) ≠ 0`, and any set `A`,

  `μ[A | C ∩ B] · μ[C | B] ≤ μ[A | B]`.

This is the honest measure-theoretic engine of the Lovász Local Lemma's inductive
step: `C` is the survival history of the current event's neighbours, `B` the
survival history of its non-neighbours. No independence or dependency-graph
hypothesis is used — the proof is a pure cancellation. Multiplying both sides by
`μ B` and telescoping the conditionals via `cond_mul_eq_inter` reduces the claim to
the monotonicity `μ (C ∩ B ∩ A) ≤ μ (B ∩ A)` (since `C ∩ B ∩ A ⊆ B ∩ A`). -/
theorem cond_inter_mul_cond_le
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hCB : μ (C ∩ B) ≠ 0) :
    μ[A | C ∩ B] * μ[C | B] ≤ μ[A | B] := by
  have hBne : μ B ≠ 0 := fun h => hCB (measure_mono_null Set.inter_subset_right h)
  have hBtop : μ B ≠ ∞ := measure_ne_top μ B
  -- cancel a common factor of `μ B` on both sides, then telescope the conditionals
  rw [← ENNReal.mul_le_mul_iff_left hBne hBtop, mul_assoc,
      cond_mul_eq_inter hB C μ, Set.inter_comm B C,
      cond_mul_eq_inter (hC.inter hB) A μ, cond_mul_eq_inter hB A μ]
  -- `C ∩ B ∩ A ⊆ B ∩ A`
  exact measure_mono (fun x hx => ⟨hx.1.2, hx.2⟩)

/-- **Conditioning-quotient bound (division form).**
The quotient shape used verbatim in Spencer's proof of the Lovász Local Lemma:

  `μ[A | C ∩ B] ≤ μ[A | B] / μ[C | B]`.

Immediate from `cond_inter_mul_cond_le` via `ENNReal.le_div_iff_mul_le`, once we
note the denominator `μ[C | B]` is strictly positive (`cond_pos_of_inter_ne_zero`)
and finite (a conditional probability, `≤ 1`). -/
theorem cond_inter_le_div
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hCB : μ (C ∩ B) ≠ 0) :
    μ[A | C ∩ B] ≤ μ[A | B] / μ[C | B] := by
  have hBne : μ B ≠ 0 := fun h => hCB (measure_mono_null Set.inter_subset_right h)
  have hpos : 0 < μ[C | B] :=
    cond_pos_of_inter_ne_zero hB (by rw [Set.inter_comm]; exact hCB)
  haveI : IsProbabilityMeasure (μ[|B]) := cond_isProbabilityMeasure hBne
  have hne_top : μ[C | B] ≠ ∞ := measure_ne_top _ _
  rw [ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl hne_top)]
  exact cond_inter_mul_cond_le hB hC hCB

/-- **LLL induction-step conclusion.**
The precise arithmetic Spencer's LLL induction produces: given a numerator bound
`μ[A | B] ≤ t` (supplied by independence of the event from the non-neighbour
history `B`) and a denominator lower bound `q ≤ μ[C | B]` (supplied by the induction
hypothesis on the neighbour history `C`), the conditional failure probability on the
full history is bounded by the ratio:

  `μ[A | C ∩ B] ≤ t / q`.

The hypothesis `q ≠ ∞ ∨ t ≠ ∞` is harmless in the LLL setting (both `t` and `q`
are `≤ 1`). Proof: `μ[A | C ∩ B] · q ≤ μ[A | C ∩ B] · μ[C | B] ≤ μ[A | B] ≤ t`,
using `cond_inter_mul_cond_le` for the middle inequality. -/
theorem cond_inter_le_of_num_den
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hCB : μ (C ∩ B) ≠ 0)
    {t q : ℝ≥0∞} (hq : q ≠ 0) (hqt : q ≠ ∞ ∨ t ≠ ∞)
    (hnum : μ[A | B] ≤ t) (hden : q ≤ μ[C | B]) :
    μ[A | C ∩ B] ≤ t / q := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl hq) hqt]
  calc μ[A | C ∩ B] * q
      ≤ μ[A | C ∩ B] * μ[C | B] := by gcongr
    _ ≤ μ[A | B] := cond_inter_mul_cond_le hB hC hCB
    _ ≤ t := hnum

/-- **Per-event failure bound below one (the chain-rule scaffold's input).**
Specialising `cond_inter_le_of_num_den` to a strict ratio `t / q < 1` gives exactly
the hypothesis `μ[Aₖ | history] < 1` that `avoidance_pos_of_failure_cond_lt_one'`
(and the quantitative bound) in the chain-rule scaffold consume. This is the bridge
from a single LLL induction step to the global avoidance conclusion: certify one
event's numerator/denominator ratio below `1`, and the scaffold turns a full family
of such bounds into positive simultaneous avoidance. -/
theorem cond_inter_lt_one_of_num_den
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hCB : μ (C ∩ B) ≠ 0)
    {t q : ℝ≥0∞} (hq : q ≠ 0) (hqt : q ≠ ∞ ∨ t ≠ ∞)
    (hnum : μ[A | B] ≤ t) (hden : q ≤ μ[C | B]) (hratio : t / q < 1) :
    μ[A | C ∩ B] < 1 :=
  lt_of_le_of_lt (cond_inter_le_of_num_den hB hC hCB hq hqt hnum hden) hratio

end LovaszLocalLemmaOQ01ConditioningQuotient
