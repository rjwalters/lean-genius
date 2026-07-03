/-
# Lovász Local Lemma — OQ-01: Exact Two-Event Inclusion–Exclusion Avoidance

Companion to `Proofs/LovaszLocalLemmaOQ01.lean` (the `d = 0` mutually independent
base case, avoidance `∏ (1 - μ Aᵢ)`) and
`Proofs/LovaszLocalLemmaOQ01UnionBound.lean` (the dependency-free first-moment
bound `μ (⋂ Aᵢᶜ) ≥ 1 - ∑ μ Aᵢ`). Those two files bracket the LLL landscape but
both *bound* the avoidance probability. This file lands the **exact** value in the
smallest genuinely-dependent regime — two events — via inclusion–exclusion.

For two measurable events `A, B` over a probability space,

  `μ (Aᶜ ∩ Bᶜ) + μ A + μ B = 1 + μ (A ∩ B)`,

i.e. `μ (Aᶜ ∩ Bᶜ) = 1 - μ A - μ B + μ (A ∩ B)` (stated additively to sidestep
truncated `ℝ≥0∞` subtraction). This is *exact*, with no independence hypothesis:
the pairwise overlap `μ (A ∩ B)` is precisely the correction the two-event union
bound `μ (Aᶜ ∩ Bᶜ) ≥ 1 - μ A - μ B` discards.

The corollary sharpens the union-bound avoidance threshold. The union bound proves
positive avoidance from `μ A + μ B < 1`; here positivity holds under the strictly
weaker `μ A + μ B < 1 + μ (A ∩ B)` — weaker by exactly the overlap `μ (A ∩ B)`,
which is nonzero precisely when the events are positively correlated / dependent.
This is the first quantitative place where *dependency helps*, foreshadowing why
the LLL can beat the global `∑ μ Aᵢ < 1` threshold.

## Main results

* `two_event_avoidance_add` : the exact inclusion–exclusion identity
  `μ (Aᶜ ∩ Bᶜ) + μ A + μ B = 1 + μ (A ∩ B)`.
* `two_event_avoidance` : positive avoidance `0 < μ (Aᶜ ∩ Bᶜ)` under the sharp
  threshold `μ A + μ B < 1 + μ (A ∩ B)`.
* `two_event_avoidance_of_union_lt` : the coarser union-bound sufficient condition
  `μ A + μ B < 1` follows as a special case, exhibiting the strict improvement.
-/
import Mathlib.Probability.Independence.Basic

open MeasureTheory
open scoped ENNReal

namespace LovaszLocalLemmaOQ01InclusionExclusion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {A B : Set Ω}

/-- **Exact two-event inclusion–exclusion avoidance identity.**
For two measurable events over a probability space, the probability that *neither*
occurs satisfies `μ (Aᶜ ∩ Bᶜ) + μ A + μ B = 1 + μ (A ∩ B)`. Equivalently
`μ (Aᶜ ∩ Bᶜ) = 1 - μ A - μ B + μ (A ∩ B)`, the exact avoidance value in the
smallest dependent regime — the additive form avoids `ℝ≥0∞` truncated subtraction.
No independence is assumed; the pairwise overlap `μ (A ∩ B)` is the exact
correction dropped by the two-event union bound. -/
theorem two_event_avoidance_add (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ (Aᶜ ∩ Bᶜ) + μ A + μ B = 1 + μ (A ∩ B) := by
  have hAB : MeasurableSet (A ∪ B) := hA.union hB
  -- avoidance is the complement of the union
  have hcompl : Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ := (Set.compl_union A B).symm
  -- complement partitions the whole space
  have h1 : μ (Aᶜ ∩ Bᶜ) + μ (A ∪ B) = 1 := by
    rw [hcompl, add_comm, measure_add_measure_compl hAB, measure_univ]
  -- inclusion–exclusion for the union
  have h2 : μ (A ∪ B) + μ (A ∩ B) = μ A + μ B := measure_union_add_inter A hB
  calc μ (Aᶜ ∩ Bᶜ) + μ A + μ B
      = μ (Aᶜ ∩ Bᶜ) + (μ A + μ B) := by rw [add_assoc]
    _ = μ (Aᶜ ∩ Bᶜ) + (μ (A ∪ B) + μ (A ∩ B)) := by rw [h2]
    _ = (μ (Aᶜ ∩ Bᶜ) + μ (A ∪ B)) + μ (A ∩ B) := by rw [add_assoc]
    _ = 1 + μ (A ∩ B) := by rw [h1]

/-- **Sharp two-event positive avoidance.**
Both events are simultaneously avoided with strictly positive probability as soon
as `μ A + μ B < 1 + μ (A ∩ B)`. This threshold is strictly weaker than the
union-bound condition `μ A + μ B < 1` whenever the overlap `μ (A ∩ B)` is positive:
the first quantitative sign that dependency (here, positive correlation) *helps*
avoid all bad events, which is the mechanism the full LLL exploits. -/
theorem two_event_avoidance (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hlt : μ A + μ B < 1 + μ (A ∩ B)) :
    0 < μ (Aᶜ ∩ Bᶜ) := by
  rw [pos_iff_ne_zero]
  intro h0
  have hid := two_event_avoidance_add (μ := μ) hA hB
  rw [h0, zero_add] at hid
  exact hlt.ne hid

/-- The coarse two-event union (first-moment) sufficient condition `μ A + μ B < 1`
is the special case of `two_event_avoidance` obtained by discarding the overlap
term `μ (A ∩ B) ≥ 0`. Recorded to make the improvement explicit: the exact identity
strictly widens the avoidance-guaranteeing region by the pairwise overlap. -/
theorem two_event_avoidance_of_union_lt (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hlt : μ A + μ B < 1) :
    0 < μ (Aᶜ ∩ Bᶜ) :=
  two_event_avoidance hA hB (lt_of_lt_of_le hlt (le_add_right le_rfl))

end LovaszLocalLemmaOQ01InclusionExclusion
