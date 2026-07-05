/-
# Lovász Local Lemma — OQ-01: Pairwise (two-event) inclusion–exclusion avoidance

The sibling entry `LovaszLocalLemmaOQ01.lean` lands the `d = 0` (mutually
independent) base case of the measure-theoretic Lovász Local Lemma, and
`LovaszLocalLemmaOQ01UnionBound.lean` gives the dependency-free first-moment
(union) bound `μ (⋂ᵢ Aᵢᶜ) ≥ 1 - Σ μ (Aᵢ)`. Both bottom out where the events carry
*no* dependency information.

This file takes the **first inductive increment beyond full independence** flagged
as an open question of OQ-01: the exact **two-event inclusion–exclusion** avoidance,
valid for *any* dependency structure. For two measurable events `A, B` in a real
probability space,

  `μ ((A ∪ B)ᶜ) + μ A + μ B = 1 + μ (A ∩ B)`,

the cancellation-free form of `μ ((A ∪ B)ᶜ) = 1 - μ A - μ B + μ (A ∩ B)` (stated
additively to sidestep the truncated subtraction of `ℝ≥0∞`). The `μ (A ∩ B)` term is
exactly the correction the union bound discards, so:

* joint avoidance is positive **iff** `μ (A ∪ B) < 1` (`avoidance_two_pos`);
* it stays positive under the *weaker* hypothesis `μ A + μ B < 1 + μ (A ∩ B)`, so
  overlap (positive dependency) strictly relaxes the union-bound threshold
  (`avoidance_two_pos_of_lt`);
* the two-event avoidance always dominates the first-moment bound
  (`avoidance_two_ge_union`);
* under independence the correction becomes `μ A · μ B`, matching the `n = 2` case
  of the base-case factorization (`avoidance_two_indep_add`).

Everything is over an arbitrary real `IsProbabilityMeasure`; fully verified,
0 sorries, 0 axioms.
-/
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LovaszLocalLemmaOQ01Pairwise

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A B : Set Ω}

/-- **Exact two-event avoidance (inclusion–exclusion, additive form).**
For any two measurable events in a probability space, the joint-avoidance
probability `μ ((A ∪ B)ᶜ)` obeys the cancellation-free inclusion–exclusion identity
`μ ((A ∪ B)ᶜ) + μ A + μ B = 1 + μ (A ∩ B)` — the additive rendering of
`μ ((A ∪ B)ᶜ) = 1 - μ A - μ B + μ (A ∩ B)`, which avoids the truncated subtraction
of `ℝ≥0∞`. -/
theorem avoidance_two_add [IsProbabilityMeasure μ]
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ ((A ∪ B)ᶜ) + μ A + μ B = 1 + μ (A ∩ B) := by
  have hcompl : μ (A ∪ B) + μ ((A ∪ B)ᶜ) = 1 := by
    rw [measure_add_measure_compl (hA.union hB), measure_univ]
  have hincl : μ (A ∪ B) + μ (A ∩ B) = μ A + μ B := measure_union_add_inter A hB
  calc μ ((A ∪ B)ᶜ) + μ A + μ B
      = μ ((A ∪ B)ᶜ) + (μ A + μ B) := by rw [add_assoc]
    _ = μ ((A ∪ B)ᶜ) + (μ (A ∪ B) + μ (A ∩ B)) := by rw [← hincl]
    _ = (μ (A ∪ B) + μ ((A ∪ B)ᶜ)) + μ (A ∩ B) := by rw [add_comm (μ (A ∪ B)) _, add_assoc]
    _ = 1 + μ (A ∩ B) := by rw [hcompl]

/-- **Two-event avoidance is positive iff the union is not almost sure.**
Two bad events — with *any* dependency structure — can be jointly avoided with
positive probability exactly when `μ (A ∪ B) < 1`. This is the honest two-event
instance of the Lovász Local Lemma conclusion `μ (⋂ Aᵢᶜ) > 0`. -/
theorem avoidance_two_pos [IsProbabilityMeasure μ]
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    0 < μ ((A ∪ B)ᶜ) ↔ μ (A ∪ B) < 1 := by
  rw [prob_compl_eq_one_sub (hA.union hB), tsub_pos_iff_lt]

/-- **Dependency-aware positivity threshold.**
Joint avoidance of two events is positive as soon as `μ A + μ B < 1 + μ (A ∩ B)`.
When the events overlap (`μ (A ∩ B) > 0`) this is strictly weaker than the
union-bound requirement `μ A + μ B < 1`: positive dependency *relaxes* the
threshold, the first quantitative sign that dependency information helps — the
phenomenon the general LLL exploits. -/
theorem avoidance_two_pos_of_lt [IsProbabilityMeasure μ]
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : μ A + μ B < 1 + μ (A ∩ B)) :
    0 < μ ((A ∪ B)ᶜ) := by
  rw [pos_iff_ne_zero]
  intro h0
  have hkey := avoidance_two_add hA hB
  rw [h0, zero_add] at hkey
  exact absurd hkey h.ne

/-- **Two-event avoidance dominates the first-moment (union) bound.**
`1 - (μ A + μ B) ≤ μ ((A ∪ B)ᶜ)`, recovering the dependency-free union bound; the
exact surplus over it is the correction term `μ (A ∩ B)` supplied by
`avoidance_two_add`. -/
theorem avoidance_two_ge_union [IsProbabilityMeasure μ]
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    1 - (μ A + μ B) ≤ μ ((A ∪ B)ᶜ) := by
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0∞) ≤ 1 + μ (A ∩ B) := le_self_add
    _ = μ ((A ∪ B)ᶜ) + μ A + μ B := (avoidance_two_add hA hB).symm
    _ = μ ((A ∪ B)ᶜ) + (μ A + μ B) := by rw [add_assoc]

/-- **Independence specialization (consistency with the `d = 0` base case).**
When `A` and `B` are independent, `μ (A ∩ B) = μ A · μ B`, so the two-event
inclusion–exclusion identity becomes the product form
`μ ((A ∪ B)ᶜ) + μ A + μ B = 1 + μ A · μ B`, i.e. `μ ((A ∪ B)ᶜ) = (1 - μ A)(1 - μ B)`.
This is exactly the `n = 2` instance of `lll_independent_meas_iInter_compl`, so the
pairwise and independent developments agree where they overlap. -/
theorem avoidance_two_indep_add [IsProbabilityMeasure μ]
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hind : IndepSet A B μ) :
    μ ((A ∪ B)ᶜ) + μ A + μ B = 1 + μ A * μ B := by
  rw [avoidance_two_add hA hB, hind.measure_inter_eq_mul]

end LovaszLocalLemmaOQ01Pairwise
