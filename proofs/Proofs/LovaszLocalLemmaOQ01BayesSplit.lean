/-
# Lovász Local Lemma — OQ-01: The Two-Block Conditioning Split (Denominator of the Induction Step)

`Proofs/LovaszLocalLemmaOQ01DependencySplit.lean` (#34107) supplies the *numerator*
half of the Erdős–Lovász dependency-graph induction step over an arbitrary subset
history: conditional probability is monotone in its numerator
(`cond_mono_num` / `cond_inter_le`), and conditioning on a survival history the event
is independent of leaves its probability unchanged
(`cond_failure_eq_measure_of_indep_subset`). Chaining these it reaches
`μ[Aᵢ ∩ (⋂_{S₁} Aⱼᶜ) | ⋂_{S₂} Aⱼᶜ] ≤ μ(Aᵢ)` — the *numerator* `Aᵢ ∩ neighbours`
conditioned on the *non-neighbour* block, bounded by `p`.

That is only half of the induction step. What the Erdős–Lovász argument actually needs
is a bound on `μ[Aᵢ | history]` where the history is the **full** survival
`(⋂_{S₁} Aⱼᶜ) ∩ (⋂_{S₂} Aⱼᶜ)` — neighbours *and* non-neighbours together — and the
bridge from the numerator bound to that full-history conditional is the Bayes step

  `μ[Aᵢ | B ∩ C]  =  μ[Aᵢ ∩ B | C] / μ[B | C]`,

which **introduces the denominator** `μ[B | C]` (the neighbour-block survival,
conditioned on the non-neighbours). No existing OQ-01 file states this split; it is the
piece that turns the numerator toolkit of #34107 into a genuine bound on the
conditional failure probability the chain-rule scaffold consumes.

This file lands that split and its consequence as clean, general, `0`-axiom / `0`-sorry
lemmas over an arbitrary probability measure, stated abstractly for events
`A B C : Set Ω` (instantiate `B = ⋂_{S₁} Aⱼᶜ`, `C = ⋂_{S₂} Aⱼᶜ`). Combined with the
non-neighbour collapse it yields the full-history form of the Spencer step,

  `μ[Aᵢ | B ∩ C] · μ[B | C] ≤ μ(Aᵢ)`,   equivalently   `μ[Aᵢ | B ∩ C] ≤ μ(Aᵢ) / μ[B | C]`,

reducing the bounded dependency-degree LLL to the single remaining estimate — the
neighbour-block survival lower bound `μ[B | C] ≥ ∏_{j∈S₁}(1 - xⱼ)`, which the LLL
strong induction supplies.

## Main results

* `cond_inter_eq_cond_cond_mul` *(the new content)* : the **two-block conditioning
  chain rule** `μ[(A ∩ B) | C] = μ[A | B ∩ C] · μ[B | C]`, for any events over any
  probability measure with `μ(B ∩ C) ≠ 0`. The Bayes identity that peels the neighbour
  block `B` off the full history conditionally on the non-neighbour block `C`, exposing
  the denominator `μ[B | C]` absent from the numerator toolkit.
* `cond_inter_le_cond` : conditioning is monotone in its event,
  `μ[(A ∩ B) | C] ≤ μ[A | C]` (abstract restatement of #34107's `cond_inter_le`,
  kept self-contained; drops the neighbour constraint `B`).
* `cond_split_le_cond` : the **full-history Spencer bound**
  `μ[A | B ∩ C] · μ[B | C] ≤ μ[A | C]` — the conditional on the *full* two-block history,
  weighted by the neighbour survival, never exceeds the non-neighbour conditional.
  This is the step #34107's numerator bound could not state.
* `cond_eq_measure_of_indepSet` : if `A` is independent of `C` (positive measure), then
  `μ[A | C] = μ(A)` (abstract form of #34107's non-neighbour collapse).
* `cond_split_le_measure_of_indep` *(flagship)* : the assembled **full-history Spencer
  step** `μ[A | B ∩ C] · μ[B | C] ≤ μ(A)` when `A` is independent of the non-neighbour
  block `C` — the bounded-degree conditional failure bound modulo the denominator
  estimate.

Only the conditioning sets `B`, `C` need be measurable. Instantiating `B`, `C` at the
neighbour / non-neighbour survival intersections is exactly the Erdős–Lovász induction;
this file supplies the denominator-introducing identity it consumes.
-/
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LovaszLocalLemmaOQ01BayesSplit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {A B C : Set Ω}

/-- **Two-block conditioning chain rule (the denominator-introducing Bayes step).**
For arbitrary events over a probability measure, conditioning on a two-block history
`B ∩ C` factors as conditioning on `B` given `C`, followed by conditioning on `A` given
the refined history `B ∩ C`:

  `μ[(A ∩ B) | C] = μ[A | B ∩ C] · μ[B | C]`.

This is the Bayes identity the Lovász Local Lemma induction runs on: with
`B = ⋂_{j∈S₁} Aⱼᶜ` the survival over `Aₖ`'s dependency neighbours and
`C = ⋂_{j∈S₂} Aⱼᶜ` the survival over its non-neighbours, it peels the neighbour block
off the history conditionally on the non-neighbour block, exposing the denominator
`μ[B | C]`. Requires the joint conditioning set `B ∩ C` to have positive measure (so the
inner conditioning is a genuine probability). Proof: `cond_apply` unfolds all three
conditionals to `(measure)⁻¹ · (intersection measure)`; the `μ(B ∩ C)` factor cancels
against its inverse (finite, nonzero over a probability measure) and the surviving
intersections agree after reassociation. -/
theorem cond_inter_eq_cond_cond_mul (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : μ (B ∩ C) ≠ 0) :
    μ[(A ∩ B) | C] = μ[A | B ∩ C] * μ[B | C] := by
  rw [cond_apply hC, cond_apply (hB.inter hC), cond_apply hC]
  -- reconcile the two intersections that carry the numerator mass
  have e2 : μ (B ∩ C ∩ A) = μ (C ∩ (A ∩ B)) := by
    congr 1
    ext x; simp only [Set.mem_inter_iff]; tauto
  have e1 : μ (C ∩ B) = μ (B ∩ C) := by rw [Set.inter_comm]
  rw [e1, e2,
    show (μ (B ∩ C))⁻¹ * μ (C ∩ (A ∩ B)) * ((μ C)⁻¹ * μ (B ∩ C))
        = ((μ (B ∩ C))⁻¹ * μ (B ∩ C)) * ((μ C)⁻¹ * μ (C ∩ (A ∩ B))) from by ring,
    ENNReal.inv_mul_cancel hBC (measure_ne_top μ _), one_mul]

/-- **Conditioning is monotone in its event.**
Dropping a constraint can only increase the conditional probability:
`μ[(A ∩ B) | C] ≤ μ[A | C]`. Elementary — `cond_apply` reduces it to
`μ (C ∩ (A ∩ B)) ≤ μ (C ∩ A)`, i.e. `measure_mono` on `C ∩ (A ∩ B) ⊆ C ∩ A`, times the
common factor `(μ C)⁻¹`. Abstract restatement of #34107's `cond_inter_le`; supplies the
inequality half of the full-history Spencer bound. -/
theorem cond_inter_le_cond (hC : MeasurableSet C) :
    μ[(A ∩ B) | C] ≤ μ[A | C] := by
  rw [cond_apply hC, cond_apply hC]
  have hsub : C ∩ (A ∩ B) ⊆ C ∩ A := fun x hx => ⟨hx.1, hx.2.1⟩
  exact mul_le_mul_left' (measure_mono hsub) _

/-- **Full-history Spencer bound (what the numerator toolkit could not state).**
Combining the two-block chain rule with event-monotonicity: the failure conditional on
the *full* two-block history `B ∩ C`, weighted by the neighbour-block survival
conditional, is at most the failure conditional on the non-neighbour block alone:

  `μ[A | B ∩ C] · μ[B | C] ≤ μ[A | C]`.

Equivalently `μ[A | B ∩ C] ≤ μ[A | C] / μ[B | C]` — the shape the Erdős–Lovász induction
uses to bound `Aₖ`'s failure probability on its survival history by its failure
probability against the non-neighbours only, deflated by the neighbour-block survival
`μ[B | C]`. Unlike #34107's `cond_failure_le_measure_of_indep_num`, the left side here
conditions on the full history `B ∩ C`, not merely the non-neighbour numerator. -/
theorem cond_split_le_cond (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : μ (B ∩ C) ≠ 0) :
    μ[A | B ∩ C] * μ[B | C] ≤ μ[A | C] := by
  rw [← cond_inter_eq_cond_cond_mul hB hC hBC]
  exact cond_inter_le_cond hC

/-- **Non-neighbour independence input.**
If `A` is independent of the (positive-measure) conditioning set `C`, then conditioning
on `C` leaves `A`'s probability unchanged: `μ[A | C] = μ(A)`. In the LLL this is applied
with `C` the survival over `Aₖ`'s *non-neighbours*, on which `Aₖ` does not depend.
Abstract form of #34107's `cond_failure_eq_measure_of_indep_subset` (there specialised
to a subset survival history); same `cond_apply` + `IndepSet.measure_inter_eq_mul`
mechanism. -/
theorem cond_eq_measure_of_indepSet (hC : MeasurableSet C) (hC0 : μ C ≠ 0)
    (hindep : IndepSet A C μ) :
    μ[A | C] = μ A := by
  rw [cond_apply hC, Set.inter_comm, hindep.measure_inter_eq_mul, mul_comm (μ A),
    ← mul_assoc, ENNReal.inv_mul_cancel hC0 (measure_ne_top μ _), one_mul]

/-- **Full-history Spencer induction step (assembled).**
When `A` is independent of the non-neighbour block `C`, the full-history Spencer bound
collapses its right-hand side to the unconditional probability:

  `μ[A | B ∩ C] · μ[B | C] ≤ μ(A)`.

Rearranged, `μ[A | B ∩ C] ≤ μ(A) / μ[B | C]`. With `A = Aₖ`, `B` the neighbour-block
survival and `C` the non-neighbour-block survival, this is *exactly* the Erdős–Lovász
bound on the conditional failure probability over the full survival history, reducing
the bounded dependency-degree LLL to the single remaining estimate — the neighbour-block
survival lower bound `μ[B | C] ≥ ∏_{j∈S₁}(1 - xⱼ)` — which the LLL strong induction
supplies. This is the step #34107's numerator-only bound stopped short of: it delivers a
bound on the conditional over the *combined* neighbour-and-non-neighbour history. -/
theorem cond_split_le_measure_of_indep (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : μ (B ∩ C) ≠ 0) (hindep : IndepSet A C μ) :
    μ[A | B ∩ C] * μ[B | C] ≤ μ A := by
  have hC0 : μ C ≠ 0 := fun h => hBC (measure_mono_null Set.inter_subset_right h)
  calc μ[A | B ∩ C] * μ[B | C]
      ≤ μ[A | C] := cond_split_le_cond hB hC hBC
    _ = μ A := cond_eq_measure_of_indepSet hC hC0 hindep

end LovaszLocalLemmaOQ01BayesSplit
