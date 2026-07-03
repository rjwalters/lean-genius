/-
# Lovász Local Lemma — OQ-01: Union-Bound (First-Moment) Avoidance Regime

Companion to `Proofs/LovaszLocalLemmaOQ01.lean`, which lands the `d = 0`
*mutually independent* base case of the measure-theoretic symmetric Lovász Local
Lemma (avoidance probability factors as `∏ (1 - μ Aᵢ)`, strictly positive when
each `μ Aᵢ < 1`). That is one extreme of the LLL landscape — full independence.

This file lands the complementary, **dependency-free** extreme: the crude
first-moment / union (Bonferroni) lower bound. For an *arbitrary* finite family of
measurable events (no independence, no bounded-dependency hypothesis whatsoever),

  `μ (⋂ i, (A i)ᶜ) ≥ 1 - ∑ i, μ (A i)`,

so all bad events are avoided with positive probability as soon as the total mass
`∑ μ (A i) < 1`. Equivalently, under a uniform bound `μ (A i) ≤ p`, the sufficient
condition is `n · p < 1` where `n = |ι|`.

These two files bracket the genuine open target of OQ-01 — the
bounded-dependency-degree symmetric LLL (`e · p · (d + 1) ≤ 1`). The LLL is
precisely the statement that a *bounded local* dependency structure lets one relax
the crude global threshold `n · p < 1` proved here to the far weaker local
threshold `e · p · (d + 1) ≤ 1`, independent of `n`. This union bound is the honest
baseline the LLL improves upon; it is elementary (a one-line consequence of
countable subadditivity), not the LLL itself.

## Main results

* `lll_union_bound_iInter_compl_ge` : the first-moment lower bound
  `1 - ∑ i, μ (A i) ≤ μ (⋂ i, (A i)ᶜ)`, for any measurable family over a
  probability space — no independence assumed.
* `lll_union_bound_avoidance` : if `∑ i, μ (A i) < 1` then `0 < μ (⋂ i, (A i)ᶜ)`.
* `lll_union_bound_avoidance_symmetric` : under a uniform bound `μ (A i) ≤ p` with
  `(|ι|) · p < 1`, the same strict-avoidance conclusion.
-/
import Mathlib.Probability.Independence.Basic

open MeasureTheory Finset
open scoped ENNReal

namespace LovaszLocalLemmaOQ01UnionBound

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {A : ι → Set Ω}

/-- **First-moment (union / Bonferroni) avoidance bound.**
For an *arbitrary* finite family of measurable events over a probability space —
no independence and no bounded-dependency hypothesis — the probability that none
of them occurs is at least `1 - ∑ μ (A i)`. This is the crude global baseline that
the Lovász Local Lemma improves upon: it needs the total mass `∑ μ (A i)` to be
small, whereas the LLL needs only the *local* dependency degree to be controlled. -/
theorem lll_union_bound_iInter_compl_ge (hA : ∀ i, MeasurableSet (A i)) :
    1 - ∑ i, μ (A i) ≤ μ (⋂ i, (A i)ᶜ) := by
  have hU : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hA
  calc 1 - ∑ i, μ (A i)
      ≤ 1 - μ (⋃ i, A i) := tsub_le_tsub_left (measure_iUnion_fintype_le μ A) 1
    _ = μ ((⋃ i, A i)ᶜ) := (prob_compl_eq_one_sub hU).symm
    _ = μ (⋂ i, (A i)ᶜ) := by rw [Set.compl_iUnion]

/-- **Positive avoidance from a small total mass (dependency-free).**
If the total probability of the bad events is subcritical (`∑ i, μ (A i) < 1`),
then all of them are simultaneously avoided with strictly positive probability,
with no independence or dependency-degree assumption. -/
theorem lll_union_bound_avoidance
    (hA : ∀ i, MeasurableSet (A i)) (hsum : ∑ i, μ (A i) < 1) :
    0 < μ (⋂ i, (A i)ᶜ) :=
  lt_of_lt_of_le (tsub_pos_iff_lt.2 hsum) (lll_union_bound_iInter_compl_ge hA)

/-- **Symmetric union-bound avoidance.**
Under a uniform bound `μ (A i) ≤ p` with `n · p < 1` (`n = |ι|` the number of bad
events), all events are avoided with positive probability. This is the crude
symmetric threshold `n · p < 1` that the symmetric LLL relaxes to the
`n`-independent local budget `e · p · (d + 1) ≤ 1`. -/
theorem lll_union_bound_avoidance_symmetric
    (hA : ∀ i, MeasurableSet (A i)) {p : ℝ≥0∞} (hbound : ∀ i, μ (A i) ≤ p)
    (hcard : (Fintype.card ι : ℝ≥0∞) * p < 1) :
    0 < μ (⋂ i, (A i)ᶜ) := by
  refine lll_union_bound_avoidance hA (lt_of_le_of_lt ?_ hcard)
  calc ∑ i, μ (A i)
      ≤ ∑ _i : ι, p := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (Fintype.card ι : ℝ≥0∞) * p := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end LovaszLocalLemmaOQ01UnionBound
