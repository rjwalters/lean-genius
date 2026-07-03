/-
# Lovász Local Lemma — OQ-01: Quantitative Avoidance Lower Bound

`Proofs/LovaszLocalLemmaOQ01ChainRule.lean` reduces the measure-theoretic LLL to a
per-event conditional bound and proves the *qualitative* conclusion
`avoidance_pos_of_failure_cond_lt_one'`: if every conditional failure probability
`μ[Aₖ | ⋂_{j<k} Aⱼᶜ]` is `< 1`, then the events are avoided with **positive**
probability. That is only the positivity half of the Lovász Local Lemma.

The LLL actually delivers a **quantitative** lower bound. This file lands it: if
every conditional failure probability is bounded by `bₖ < 1`, then

  `∏ₖ (1 - bₖ) ≤ μ (⋂ᵢ Aᵢᶜ)`.

This is the honest measure-theoretic analogue of the rational-surrogate
`general_lll` in the gallery proof `LovaszLocalLemma.lean` (which merely records
`∏ (1 - xᵢ) > 0` over `ℚ`): here `∏ (1 - bₖ)` is a genuine *lower bound on the real
avoidance probability over an arbitrary probability space*, not a stand-alone
budget. Positivity (`avoidance_pos_of_failure_cond_lt_one'`) is recovered as the
special case where the product is itself positive, but the quantitative bound is
strictly stronger — it pins how large the avoidance probability must be.

The proof reuses the chain-rule scaffold with no new probabilistic input: the
survival product `μ (⋂ Aᵢᶜ) = ∏ μ[Aₖᶜ | history]` factors the avoidance
probability, history positivity is automatic from the failure bounds
(`hist_pos_of_failure_cond_lt_one`), and on each positive history the survival
conditional is `1 - μ[Aₖ | history] ≥ 1 - bₖ` (antitone truncated subtraction).
Monotonicity of the finite `ℝ≥0∞` product finishes.

## Main results

* `avoidance_ge_prod_one_sub` : the quantitative LLL lower bound
  `∏ₖ (1 - bₖ) ≤ μ (⋂ᵢ Aᵢᶜ)` from per-event conditional failure bounds `bₖ < 1`.
* `avoidance_ge_one_sub_pow` : the symmetric specialisation — a uniform bound
  `μ[Aₖ | history] ≤ p < 1` gives `(1 - p)ⁿ ≤ μ (⋂ᵢ Aᵢᶜ)`.
* `avoidance_pos_of_prod_one_sub_pos` : the quantitative bound recovers
  positivity, since `0 < ∏ₖ (1 - bₖ)` whenever every `bₖ < 1`.

No independence hypothesis is used anywhere; everything is `Finset.range`-indexed
over an arbitrary `IsProbabilityMeasure`.
-/
import Proofs.LovaszLocalLemmaOQ01ChainRule

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
open LovaszLocalLemmaOQ01ChainRule

namespace LovaszLocalLemmaOQ01Quantitative

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {A : ℕ → Set Ω}

/-- **Quantitative Lovász Local Lemma lower bound.**
If every conditional failure probability `μ[Aₖ | ⋂_{j<k} Aⱼᶜ]` is bounded by some
`bₖ < 1`, then the avoidance probability is at least the product of the survival
budgets:

  `∏ₖ (1 - bₖ) ≤ μ (⋂ᵢ Aᵢᶜ)`.

This is the honest measure-theoretic form of the LLL conclusion `μ (⋂ Aᵢᶜ) ≥
∏ (1 - xᵢ)` — a real lower bound on the avoidance probability, not a rational
budget surrogate. It strengthens `avoidance_pos_of_failure_cond_lt_one'` (which
gives only positivity) to a quantitative estimate.

Proof: the survival-product identity `avoidance_eq_prod_survival_cond` rewrites the
avoidance probability as `∏ₖ μ[Aₖᶜ | history]`; history positivity is automatic
(`hist_pos_of_failure_cond_lt_one`), so on each history the survival conditional is
`1 - μ[Aₖ | history] ≥ 1 - bₖ` by antitonicity of truncated subtraction; monotonicity
of the finite `ℝ≥0∞` product closes it. -/
theorem avoidance_ge_prod_one_sub (hA : ∀ i, MeasurableSet (A i)) (n : ℕ)
    (b : ℕ → ℝ≥0∞) (hb : ∀ k ∈ Finset.range n, b k < 1)
    (hfail : ∀ k ∈ Finset.range n, μ[A k | ⋂ j ∈ Finset.range k, (A j)ᶜ] ≤ b k) :
    ∏ k ∈ Finset.range n, (1 - b k) ≤ μ (⋂ i ∈ Finset.range n, (A i)ᶜ) := by
  rw [avoidance_eq_prod_survival_cond hA]
  refine Finset.prod_le_prod' fun k hk => ?_
  -- membership propagation: for `m < k` (`< n`) the hypotheses at `m` still apply
  have hkn : k < n := Finset.mem_range.mp hk
  have hposk : μ (⋂ j ∈ Finset.range k, (A j)ᶜ) ≠ 0 :=
    hist_pos_of_failure_cond_lt_one hA k fun m hm =>
      lt_of_le_of_lt (hfail m (Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hm) hkn)))
        (hb m (Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hm) hkn)))
  -- on the positive history, survival = 1 - failure ≥ 1 - bₖ
  rw [survival_cond_eq_one_sub hA k hposk]
  exact tsub_le_tsub_left (hfail k hk) 1

/-- **Symmetric quantitative LLL bound.**
If every conditional failure probability is bounded by a single uniform `p < 1`,
then `(1 - p)ⁿ ≤ μ (⋂ᵢ Aᵢᶜ)`. This is the symmetric-regime specialisation of
`avoidance_ge_prod_one_sub` and the quantitative shape the symmetric LLL produces
(under `e·p·(d+1) ≤ 1` the induction certifies each conditional failure `≤ p`). -/
theorem avoidance_ge_one_sub_pow (hA : ∀ i, MeasurableSet (A i)) (n : ℕ) (p : ℝ≥0∞)
    (hp : p < 1)
    (hfail : ∀ k ∈ Finset.range n, μ[A k | ⋂ j ∈ Finset.range k, (A j)ᶜ] ≤ p) :
    (1 - p) ^ n ≤ μ (⋂ i ∈ Finset.range n, (A i)ᶜ) := by
  have h := avoidance_ge_prod_one_sub hA n (fun _ => p) (fun _ _ => hp) hfail
  simpa [Finset.prod_const, Finset.card_range] using h

/-- **Positivity recovered from the quantitative bound.**
Since every `bₖ < 1` makes each survival budget `1 - bₖ` strictly positive, the
product lower bound `∏ (1 - bₖ)` is itself positive, so
`avoidance_ge_prod_one_sub` re-derives `avoidance_pos_of_failure_cond_lt_one'` as a
corollary — the qualitative LLL is the quantitative one read at the coarsest
resolution. -/
theorem avoidance_pos_of_prod_one_sub_pos (hA : ∀ i, MeasurableSet (A i)) (n : ℕ)
    (b : ℕ → ℝ≥0∞) (hb : ∀ k ∈ Finset.range n, b k < 1)
    (hfail : ∀ k ∈ Finset.range n, μ[A k | ⋂ j ∈ Finset.range k, (A j)ᶜ] ≤ b k) :
    0 < μ (⋂ i ∈ Finset.range n, (A i)ᶜ) := by
  refine lt_of_lt_of_le ?_ (avoidance_ge_prod_one_sub hA n b hb hfail)
  rw [zero_lt_iff, Finset.prod_ne_zero_iff]
  intro k hk
  rw [Ne, tsub_eq_zero_iff_le, not_le]
  exact hb k hk

end LovaszLocalLemmaOQ01Quantitative
