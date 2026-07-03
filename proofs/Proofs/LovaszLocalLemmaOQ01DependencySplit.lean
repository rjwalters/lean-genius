/-
# Lovász Local Lemma — OQ-01: Subset-History Toolkit for the Dependency-Graph Step

`Proofs/LovaszLocalLemmaOQ01ChainRule.lean` reduces the measure-theoretic LLL to a
per-event conditional bound over the **prefix** history `⋂_{j<k} Aⱼᶜ`, and
`Proofs/LovaszLocalLemmaOQ01Quantitative.lean` converts such bounds into avoidance
estimates. The genuine *content* of the Lovász Local Lemma — the Erdős–Lovász
induction that produces those per-event bounds from a bounded **dependency degree** —
does not live over prefix histories at all. Its induction step conditions on the
survival of an **arbitrary subset** `S` of the other events, and splits `S` into the
*neighbours* and *non-neighbours* of the event under scrutiny. Every existing OQ-01
file works exclusively over `Finset.range`-indexed prefixes and so cannot even state
that step.

This file supplies the two per-event moves of the dependency-graph induction step over
**arbitrary finite subset histories** `⋂_{j∈S} Aⱼᶜ`, each proved unconditionally or
from local independence:

1. **Numerator monotonicity** (`cond_mono_num`): conditional probability is monotone in
   its numerator, `E ⊆ F → μ[E | H] ≤ μ[F | H]`, for any measurable conditioning set
   `H`. There is *no* such lemma in Mathlib. It is the step by which the induction drops
   the neighbour factor: `μ[Aᵢ ∩ (⋂_{S₁} Aⱼᶜ) | H] ≤ μ[Aᵢ | H]`
   (`cond_inter_le`).

2. **Non-neighbour collapse over an arbitrary subset** (`cond_failure_eq_measure_of_indep_subset`):
   if `Aᵢ` is independent of the survival history `⋂_{j∈S} Aⱼᶜ` of an *arbitrary* finite
   `S` (of positive measure), the conditional failure probability equals the
   unconditional one, `μ[Aᵢ | ⋂_{j∈S} Aⱼᶜ] = μ(Aᵢ)`. This is the arbitrary-subset
   generalisation of the prefix-only non-neighbour step: in the dependency graph the
   non-neighbours of `Aᵢ` form an unstructured set `S₂`, never a prefix, so the prefix
   version cannot express the reduction the induction actually performs.

Combining the two gives the **numerator half of the induction step over an arbitrary
subset history** (`cond_failure_le_measure_of_indep_num`): conditioning `Aᵢ` on the
survival of a *sub*-history it is independent of only *increases* its budget, so once
the neighbour factor is dropped the failure probability is at most `μ(Aᵢ)`.

## Main results

* `cond_mono_num` : `E ⊆ F → μ[E | H] ≤ μ[F | H]` — conditional probability is monotone
  in the numerator (new; not in Mathlib).
* `cond_inter_le` : `μ[E ∩ F | H] ≤ μ[E | H]` — the neighbour-factor drop.
* `measurableSet_survival` : `MeasurableSet (⋂ j ∈ S, (A j)ᶜ)` for any `Finset` `S`.
* `cond_failure_eq_measure_of_indep_subset` : the arbitrary-subset non-neighbour
  collapse `μ[Aᵢ | ⋂_{j∈S} Aⱼᶜ] = μ(Aᵢ)`.
* `cond_failure_le_measure_of_indep_num` : conditioning `Aᵢ` on the survival of an
  independent sub-history `S₂` and any extra events `T` gives failure `≤ μ(Aᵢ)`.

What remains open (the actual LLL induction) is the *recursive denominator lower bound*
`μ[⋂_{S₁} Aⱼᶜ | ⋂_{S₂} Aⱼᶜ] ≥ ∏_{j∈S₁}(1 - xⱼ)`, which combines these ingredients across
a well-founded recursion on `|S|`. This file isolates exactly the unconditional /
local-independence parts of that step.

Everything is over an arbitrary `IsProbabilityMeasure`; no independence is assumed except
where explicitly hypothesised.
-/
import Proofs.LovaszLocalLemmaOQ01ChainRule
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace LovaszLocalLemmaOQ01DependencySplit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {A : ℕ → Set Ω} {E F H : Set Ω}

/-- **Conditional probability is monotone in the numerator.**
For any measurable conditioning set `H`, if `E ⊆ F` then `μ[E | H] ≤ μ[F | H]`.

Mathlib has no monotonicity lemma for `cond` in the conditioned event, yet it is the
elementary workhorse of the Lovász Local Lemma induction: the induction bounds the
conditional failure of an event by *dropping* the neighbour-survival factor from the
numerator, which is exactly an application of this inequality.

Proof: `cond_apply` unfolds both sides to `(μ H)⁻¹ * μ (H ∩ ·)`; `H ∩ E ⊆ H ∩ F`, so
`measure_mono` and left-multiplication by the common factor `(μ H)⁻¹` finish. -/
theorem cond_mono_num (hH : MeasurableSet H) (hEF : E ⊆ F) :
    μ[E | H] ≤ μ[F | H] := by
  rw [cond_apply hH μ E, cond_apply hH μ F]
  gcongr

/-- **Neighbour-factor drop.**
Intersecting the numerator with any set can only decrease the conditional probability:
`μ[E ∩ F | H] ≤ μ[E | H]`. The special case `cond_mono_num Set.inter_subset_left` used
by the LLL induction to discard the survival of `Aᵢ`'s neighbours from the numerator. -/
theorem cond_inter_le (hH : MeasurableSet H) :
    μ[E ∩ F | H] ≤ μ[E | H] :=
  cond_mono_num hH Set.inter_subset_left

/-- The survival history of an **arbitrary finite** index set is measurable. The
subset-indexed analogue of `LovaszLocalLemmaOQ01ChainRule.measurableSet_hist` (which is
`Finset.range`-only). -/
theorem measurableSet_survival (hA : ∀ i, MeasurableSet (A i)) (S : Finset ℕ) :
    MeasurableSet (⋂ j ∈ S, (A j)ᶜ) :=
  Finset.measurableSet_biInter _ (fun b _ => (hA b).compl)

variable [IsProbabilityMeasure μ]

/-- **Non-neighbour collapse over an arbitrary subset history.**
If the event `Aᵢ` is independent of the survival history `⋂_{j∈S} Aⱼᶜ` of an *arbitrary*
finite set `S` (of positive measure), then its conditional failure probability collapses
to the unconditional one:

  `μ[Aᵢ | ⋂_{j∈S} Aⱼᶜ] = μ(Aᵢ)`.

This is the arbitrary-subset form of the Lovász Local Lemma's non-neighbour step. In the
dependency graph the events *not* adjacent to `Aᵢ` form an unstructured subset `S₂` — not
a prefix — so this is the version the induction genuinely needs; the prefix-only variant
cannot state it. Proof: `cond_apply` unfolds the conditional as `(μ H)⁻¹ · μ(H ∩ Aᵢ)`,
`IndepSet.measure_inter_eq_mul` factors `μ(Aᵢ ∩ H) = μ(Aᵢ)·μ H`, and the finite nonzero
`μ H` cancels. -/
theorem cond_failure_eq_measure_of_indep_subset (hA : ∀ i, MeasurableSet (A i))
    (S : Finset ℕ) (i : ℕ) (hpos : μ (⋂ j ∈ S, (A j)ᶜ) ≠ 0)
    (hindep : IndepSet (A i) (⋂ j ∈ S, (A j)ᶜ) μ) :
    μ[A i | ⋂ j ∈ S, (A j)ᶜ] = μ (A i) := by
  have hHmeas : MeasurableSet (⋂ j ∈ S, (A j)ᶜ) := measurableSet_survival hA S
  rw [cond_apply hHmeas, Set.inter_comm, hindep.measure_inter_eq_mul,
      mul_comm (μ (A i)) _, ← mul_assoc,
      ENNReal.inv_mul_cancel hpos (measure_ne_top μ _), one_mul]

/-- **Numerator half of the dependency-graph induction step.**
Let `S₂` be the non-neighbours of `Aᵢ` (independent of `Aᵢ`) and `T` any further events,
with `S₂` of positive survival measure. Conditioning `Aᵢ` on the survival of `S₂`
*together with* the extra events `T` keeps its failure probability at most `μ(Aᵢ)`:

  `μ[Aᵢ ∩ (⋂_{j∈T} Aⱼᶜ) | ⋂_{j∈S₂} Aⱼᶜ] ≤ μ(Aᵢ)`.

This packages the two moves — drop the neighbour factor `T` from the numerator
(`cond_inter_le`), then collapse the independent sub-history to the unconditional
probability (`cond_failure_eq_measure_of_indep_subset`). It is the numerator bound the
LLL induction feeds into the recursive denominator estimate (still open). -/
theorem cond_failure_le_measure_of_indep_num (hA : ∀ i, MeasurableSet (A i))
    (S₂ T : Finset ℕ) (i : ℕ) (hpos : μ (⋂ j ∈ S₂, (A j)ᶜ) ≠ 0)
    (hindep : IndepSet (A i) (⋂ j ∈ S₂, (A j)ᶜ) μ) :
    μ[A i ∩ (⋂ j ∈ T, (A j)ᶜ) | ⋂ j ∈ S₂, (A j)ᶜ] ≤ μ (A i) := by
  calc μ[A i ∩ (⋂ j ∈ T, (A j)ᶜ) | ⋂ j ∈ S₂, (A j)ᶜ]
      ≤ μ[A i | ⋂ j ∈ S₂, (A j)ᶜ] := cond_inter_le (measurableSet_survival hA S₂)
    _ = μ (A i) := cond_failure_eq_measure_of_indep_subset hA S₂ i hpos hindep

end LovaszLocalLemmaOQ01DependencySplit
