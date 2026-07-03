/-
# Lovász Local Lemma — OQ-01: Conditional-Probability Chain Rule for Avoidance

The gallery proof `LovaszLocalLemma.lean` develops the *symmetric* LLL entirely
over `ℚ` as a combinatorial-budget surrogate; its `general_lll` only records the
elementary fact `∏ (1 - xᵢ) > 0`. The authoritative OQ-01 goal is the genuine
**measure-theoretic** LLL over a real probability space, where the content is the
inequality `μ (⋂ᵢ Aᵢᶜ) ≥ ∏ (1 - xᵢ) > 0` — the *avoidance probability* is
positive. `LovaszLocalLemmaOQ01.lean` lands the `d = 0` (mutually independent)
base case; `LovaszLocalLemmaOQ01UnionBound.lean` lands the dependency-free
first-moment extreme.

This file lands the **exact skeleton of the general LLL induction**: the
*conditional-probability chain rule* for a finite ordered family of events,

  `μ (⋂ᵢ Aᵢ) = ∏ₖ μ[Aₖ | ⋂_{j<k} Aⱼ]`,

which holds for **any** measurable family over **any** probability measure — no
independence, no dependency graph, no LLL hypothesis. Specialised to the
complements it gives the *survival-probability product form*

  `μ (⋂ᵢ Aᵢᶜ) = ∏ₖ μ[Aₖᶜ | ⋂_{j<k} Aⱼᶜ]`,

and hence the **avoidance-positivity criterion**: the events can be avoided
simultaneously with positive probability **iff** every conditional survival
probability `μ[Aₖᶜ | ⋂_{j<k} Aⱼᶜ]` is nonzero. This is precisely the reduction
that the Lovász Local Lemma discharges: the LLL induction's entire job is to
prove each conditional failure probability `μ[Aₖ | ⋂_{j<k} Aⱼᶜ]` bounded below 1
(equivalently, each survival probability positive), and this file supplies the
measure-theoretic bridge from that per-event bound to the global conclusion.

## Main results

* `cond_chain_avoidance` : the chain rule `μ (⋂ i∈range n, A i) =
  ∏ k∈range n, μ[A k | ⋂ j∈range k, A j]`, for an arbitrary measurable family
  over a probability measure.
* `avoidance_eq_prod_survival_cond` : the complement/survival form
  `μ (⋂ i∈range n, (A i)ᶜ) = ∏ k∈range n, μ[(A k)ᶜ | ⋂ j∈range k, (A j)ᶜ]`.
* `avoidance_pos_iff` : `0 < μ (⋂ i∈range n, (A i)ᶜ)` **iff** every survival
  conditional is nonzero — the LLL reduction target.
* `survival_cond_eq_one_sub` : on a positive-measure history the survival
  conditional is `1 - ` the failure conditional, connecting the criterion to the
  usual LLL bound `μ[A k | history] < 1`.
* `avoidance_pos_of_failure_cond_lt_one` : if every history has positive measure
  and every conditional failure probability is `< 1`, avoidance is positive —
  the exact shape the LLL induction produces.

Everything is `Finset.range`-indexed (an explicit total order on the events, as
the chain rule requires) and lives over an arbitrary `IsProbabilityMeasure`.
No independence hypothesis is used anywhere.
-/
import Mathlib.Probability.ConditionalProbability

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace LovaszLocalLemmaOQ01ChainRule

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {A : ℕ → Set Ω}

/-- Each finite history is measurable (a finite intersection of measurable sets). -/
theorem measurableSet_hist (hA : ∀ i, MeasurableSet (A i)) (n : ℕ) :
    MeasurableSet (⋂ j ∈ Finset.range n, A j) :=
  Finset.measurableSet_biInter _ (fun b _ => hA b)

/-- **Conditional-probability chain rule (avoidance skeleton of the LLL).**
For an arbitrary measurable family `A : ℕ → Set Ω` over a probability measure, the
probability of the intersection of the first `n` events factors as the product of
the conditional probabilities of each event given all earlier ones:

  `μ (⋂ i∈range n, A i) = ∏ k∈range n, μ[A k | ⋂ j∈range k, A j]`.

No independence is assumed — this is the pure chain rule, the exact identity the
Lovász Local Lemma induction fills in term by term. -/
theorem cond_chain_avoidance (hA : ∀ i, MeasurableSet (A i)) (n : ℕ) :
    μ (⋂ i ∈ Finset.range n, A i)
      = ∏ k ∈ Finset.range n, μ[A k | ⋂ j ∈ Finset.range k, A j] := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- history at `n+1` splits off the newest event `A n`
    have hsplit : (⋂ i ∈ Finset.range (n + 1), A i)
        = (⋂ i ∈ Finset.range n, A i) ∩ A n := by
      rw [Finset.range_add_one]
      rw [Finset.set_biInter_insert, Set.inter_comm]
    rw [hsplit, Finset.prod_range_succ, ← ih]
    -- the telescoping step: μ(history ∩ A n) = μ(history) · μ[A n | history]
    rw [mul_comm]
    exact (cond_mul_eq_inter (measurableSet_hist hA n) (A n) μ).symm

/-- **Survival-probability product form.**
Applying the chain rule to the complements gives the avoidance probability as a
product of conditional *survival* probabilities:

  `μ (⋂ i∈range n, (A i)ᶜ) = ∏ k∈range n, μ[(A k)ᶜ | ⋂ j∈range k, (A j)ᶜ]`.

This is the genuine measure-theoretic LLL identity (the honest analogue of the
rational surrogate's `∏ (1 - xᵢ)`): the avoidance probability is exactly the
product of per-event conditional survival probabilities. -/
theorem avoidance_eq_prod_survival_cond (hA : ∀ i, MeasurableSet (A i)) (n : ℕ) :
    μ (⋂ i ∈ Finset.range n, (A i)ᶜ)
      = ∏ k ∈ Finset.range n, μ[(A k)ᶜ | ⋂ j ∈ Finset.range k, (A j)ᶜ] :=
  cond_chain_avoidance (fun i => (hA i).compl) n

/-- **Avoidance-positivity criterion (the LLL reduction target).**
The first `n` events can be avoided simultaneously with strictly positive
probability **iff** every conditional survival probability is nonzero. Since the
avoidance probability is the product of these conditionals (over a probability
measure they are automatically finite, `≤ 1`), positivity of the product is
equivalent to nonvanishing of each factor. The Lovász Local Lemma's role is
exactly to certify the right-hand side. -/
theorem avoidance_pos_iff (hA : ∀ i, MeasurableSet (A i)) (n : ℕ) :
    0 < μ (⋂ i ∈ Finset.range n, (A i)ᶜ)
      ↔ ∀ k ∈ Finset.range n, μ[(A k)ᶜ | ⋂ j ∈ Finset.range k, (A j)ᶜ] ≠ 0 := by
  rw [avoidance_eq_prod_survival_cond hA, zero_lt_iff, Finset.prod_ne_zero_iff]

/-- On a positive-measure history the conditional *survival* probability is the
complement of the conditional *failure* probability:
`μ[(A k)ᶜ | history] = 1 - μ[A k | history]`. This is the bridge from the usual
LLL bound (each conditional failure probability `< 1`) to the survival-positivity
form used by `avoidance_pos_iff`. Requires the history to have positive measure,
so that conditioning yields a genuine probability measure. -/
theorem survival_cond_eq_one_sub (hA : ∀ i, MeasurableSet (A i)) (k : ℕ)
    (hpos : μ (⋂ j ∈ Finset.range k, (A j)ᶜ) ≠ 0) :
    μ[(A k)ᶜ | ⋂ j ∈ Finset.range k, (A j)ᶜ]
      = 1 - μ[A k | ⋂ j ∈ Finset.range k, (A j)ᶜ] := by
  haveI : IsProbabilityMeasure (μ[|⋂ j ∈ Finset.range k, (A j)ᶜ]) :=
    cond_isProbabilityMeasure hpos
  exact prob_compl_eq_one_sub (hA k)

/-- **Sufficient LLL avoidance condition.**
If every conditional failure probability `μ[A k | ⋂_{j<k} (A j)ᶜ]` is `< 1` and
every history has positive measure, then all events are avoided with positive
probability. This is precisely the shape the LLL induction delivers: the
induction certifies each conditional failure probability bounded below 1 (in the
symmetric regime, `≤ 2p < 1` under `e·p·(d+1) ≤ 1`), from which global avoidance
positivity follows via the survival product. -/
theorem avoidance_pos_of_failure_cond_lt_one (hA : ∀ i, MeasurableSet (A i)) (n : ℕ)
    (hpos : ∀ k ∈ Finset.range n, μ (⋂ j ∈ Finset.range k, (A j)ᶜ) ≠ 0)
    (hfail : ∀ k ∈ Finset.range n, μ[A k | ⋂ j ∈ Finset.range k, (A j)ᶜ] < 1) :
    0 < μ (⋂ i ∈ Finset.range n, (A i)ᶜ) := by
  rw [avoidance_pos_iff hA]
  intro k hk
  rw [survival_cond_eq_one_sub hA k (hpos k hk)]
  -- `1 - c ≠ 0` for `c < 1` in `ℝ≥0∞`
  rw [Ne, tsub_eq_zero_iff_le, not_le]
  exact hfail k hk

end LovaszLocalLemmaOQ01ChainRule
