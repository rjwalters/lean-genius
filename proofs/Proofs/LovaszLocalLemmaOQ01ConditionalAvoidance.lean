/-
# Lovász Local Lemma — OQ-01: Conditional (Relative) Quantitative Avoidance Bound

`Proofs/LovaszLocalLemmaOQ01Quantitative.lean` proves the flagship quantitative
avoidance bound `∏ₖ (1 - bₖ) ≤ μ (⋂ᵢ Aᵢᶜ)` from per-event *conditional* failure
bounds `μ[Aₖ | ⋂_{j<k} Aⱼᶜ] ≤ bₖ < 1`. That statement lives over the ambient
measure `μ`. The genuine Erdős–Lovász induction, however, never estimates a bare
avoidance probability: its **denominator recursion** lower-bounds the survival of
one block of events *conditioned on the survival of another* —

  `μ[⋂_{j∈S₁} Aⱼᶜ | ⋂_{j∈S₂} Aⱼᶜ] ≥ ∏_{j∈S₁} (1 - xⱼ)`.

`Proofs/LovaszLocalLemmaOQ01DependencySplit.lean` isolated the numerator half of the
induction step; this file supplies the **relative quantitative bound** the
denominator recursion is built from: the exact analogue of
`avoidance_ge_prod_one_sub`, but with *every* probability taken relative to a fixed
background event `H` (in the recursion, `H = ⋂_{j∈S₂} Aⱼᶜ`).

The proof adds no new probabilistic content — it *transports* the flagship
unconditional bound along the conditioning map. Conditioning on `H` yields a genuine
probability measure `μ[·|H]` (`cond_isProbabilityMeasure`, valid since `μ H ≠ 0` and
`μ` is finite); the tower property `cond_cond_eq_cond_inter`
(`μ[·|H][·|G] = μ[·|H ∩ G]`) identifies its internal conditionals with the
background-relative conditionals `μ[Aₖ | (⋂_{j<k} Aⱼᶜ) ∩ H]`; and the avoidance
probability under `μ[·|H]` is by definition `μ[⋂ᵢ Aᵢᶜ | H]`. Applying
`avoidance_ge_prod_one_sub` to `μ[·|H]` therefore delivers the relative bound
verbatim.

This is precisely the primitive the LLL denominator recursion invokes: fix the
non-neighbour survival `H`, order the block `S₁` as a prefix `range n`, and the
relative chain rule / quantitative bound gives `∏(1 - xⱼ)` from the per-factor
conditional bounds. What remains open is the well-founded recursion that *supplies*
those per-factor bounds (each conditioning set is strictly smaller, so the LLL
inductive hypothesis applies); this file removes the "condition on a background
event" obstacle that blocked reusing the prefix scaffold inside that recursion.

## Main results

* `cond_avoidance_ge_prod_one_sub` : the relative quantitative bound
  `∏ₖ (1 - bₖ) ≤ μ[⋂ᵢ Aᵢᶜ | H]` from background-relative conditional failure
  bounds `μ[Aₖ | (⋂_{j<k} Aⱼᶜ) ∩ H] ≤ bₖ < 1`.
* `cond_avoidance_ge_one_sub_pow` : the symmetric specialisation
  `(1 - p)ⁿ ≤ μ[⋂ᵢ Aᵢᶜ | H]` under a uniform relative bound `≤ p < 1`.
* `cond_avoidance_pos_of_prod_one_sub_pos` : positivity of the relative avoidance
  probability, `0 < μ[⋂ᵢ Aᵢᶜ | H]`, whenever every `bₖ < 1`.

No independence hypothesis is used; everything is `Finset.range`-indexed over an
arbitrary `IsProbabilityMeasure`, relative to an arbitrary positive-measure
background event.
-/
import Proofs.LovaszLocalLemmaOQ01Quantitative

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
open LovaszLocalLemmaOQ01ChainRule
open LovaszLocalLemmaOQ01Quantitative

namespace LovaszLocalLemmaOQ01ConditionalAvoidance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {A : ℕ → Set Ω}

/-- **Conditional (relative) quantitative Lovász Local Lemma bound.**
Fix a background event `H` of positive measure. If every conditional failure
probability *relative to `H`* is bounded,

  `μ[Aₖ | (⋂_{j<k} Aⱼᶜ) ∩ H] ≤ bₖ < 1`   for all `k < n`,

then the avoidance probability relative to `H` is at least the survival-budget
product:

  `∏ₖ (1 - bₖ) ≤ μ[⋂ᵢ Aᵢᶜ | H]`.

This is `avoidance_ge_prod_one_sub` transported to the conditioned probability
measure `μ[·|H]`: it is the exact primitive the Erdős–Lovász **denominator
recursion** invokes, where `H = ⋂_{j∈S₂} Aⱼᶜ` is the survival of the non-neighbours
and the `Aₖ` range over an ordered block `S₁`.

Proof: `cond_isProbabilityMeasure` makes `μ[·|H]` a probability measure; the tower
property `cond_cond_eq_cond_inter` rewrites each internal conditional
`μ[·|H][Aₖ | ⋂_{j<k} Aⱼᶜ]` as the background-relative conditional
`μ[Aₖ | H ∩ ⋂_{j<k} Aⱼᶜ]`, so the hypotheses of `avoidance_ge_prod_one_sub`
(applied to `μ[·|H]`) are exactly the relative bounds; its conclusion
`∏ (1 - bₖ) ≤ μ[·|H] (⋂ Aᵢᶜ)` is definitionally the claim. -/
theorem cond_avoidance_ge_prod_one_sub (hA : ∀ i, MeasurableSet (A i))
    (H : Set Ω) (hH : MeasurableSet H) (hHne : μ H ≠ 0) (n : ℕ)
    (b : ℕ → ℝ≥0∞) (hb : ∀ k ∈ Finset.range n, b k < 1)
    (hfail : ∀ k ∈ Finset.range n,
      μ[A k | (⋂ j ∈ Finset.range k, (A j)ᶜ) ∩ H] ≤ b k) :
    ∏ k ∈ Finset.range n, (1 - b k) ≤ μ[(⋂ i ∈ Finset.range n, (A i)ᶜ) | H] := by
  haveI : IsProbabilityMeasure (μ[|H]) := cond_isProbabilityMeasure hHne
  -- The conditionals of the conditioned measure `μ[·|H]` are the background-relative
  -- conditionals, via the tower property `μ[·|H][·|G] = μ[·|H ∩ G]`.
  have hfail' : ∀ k ∈ Finset.range n,
      (μ[|H])[A k | ⋂ j ∈ Finset.range k, (A j)ᶜ] ≤ b k := by
    intro k hk
    have hGk : MeasurableSet (⋂ j ∈ Finset.range k, (A j)ᶜ) :=
      measurableSet_hist (fun i => (hA i).compl) k
    rw [cond_cond_eq_cond_inter hH hGk μ, Set.inter_comm H]
    exact hfail k hk
  calc ∏ k ∈ Finset.range n, (1 - b k)
      ≤ (μ[|H]) (⋂ i ∈ Finset.range n, (A i)ᶜ) :=
        avoidance_ge_prod_one_sub hA n b hb hfail'
    _ = μ[(⋂ i ∈ Finset.range n, (A i)ᶜ) | H] := rfl

/-- **Symmetric relative quantitative bound.**
The uniform specialisation of `cond_avoidance_ge_prod_one_sub`: a single background-
relative bound `μ[Aₖ | (⋂_{j<k} Aⱼᶜ) ∩ H] ≤ p < 1` gives
`(1 - p)ⁿ ≤ μ[⋂ᵢ Aᵢᶜ | H]`. This is the shape the symmetric LLL produces inside the
denominator recursion (each relative conditional bounded by `2p` under
`e·p·(d+1) ≤ 1`). -/
theorem cond_avoidance_ge_one_sub_pow (hA : ∀ i, MeasurableSet (A i))
    (H : Set Ω) (hH : MeasurableSet H) (hHne : μ H ≠ 0) (n : ℕ) (p : ℝ≥0∞)
    (hp : p < 1)
    (hfail : ∀ k ∈ Finset.range n,
      μ[A k | (⋂ j ∈ Finset.range k, (A j)ᶜ) ∩ H] ≤ p) :
    (1 - p) ^ n ≤ μ[(⋂ i ∈ Finset.range n, (A i)ᶜ) | H] := by
  have h := cond_avoidance_ge_prod_one_sub hA H hH hHne n (fun _ => p)
    (fun _ _ => hp) hfail
  simpa [Finset.prod_const, Finset.card_range] using h

/-- **Positivity of the relative avoidance probability.**
Since every `bₖ < 1` makes each survival budget `1 - bₖ` strictly positive, the
relative avoidance probability `μ[⋂ᵢ Aᵢᶜ | H]` is positive. This is the conditional
analogue of `avoidance_pos_of_prod_one_sub_pos`, and it is exactly the statement the
denominator recursion needs to keep every conditioning set of positive measure as it
descends. -/
theorem cond_avoidance_pos_of_prod_one_sub_pos (hA : ∀ i, MeasurableSet (A i))
    (H : Set Ω) (hH : MeasurableSet H) (hHne : μ H ≠ 0) (n : ℕ)
    (b : ℕ → ℝ≥0∞) (hb : ∀ k ∈ Finset.range n, b k < 1)
    (hfail : ∀ k ∈ Finset.range n,
      μ[A k | (⋂ j ∈ Finset.range k, (A j)ᶜ) ∩ H] ≤ b k) :
    0 < μ[(⋂ i ∈ Finset.range n, (A i)ᶜ) | H] := by
  refine lt_of_lt_of_le ?_ (cond_avoidance_ge_prod_one_sub hA H hH hHne n b hb hfail)
  rw [zero_lt_iff, Finset.prod_ne_zero_iff]
  intro k hk
  rw [Ne, tsub_eq_zero_iff_le, not_le]
  exact hb k hk

end LovaszLocalLemmaOQ01ConditionalAvoidance
