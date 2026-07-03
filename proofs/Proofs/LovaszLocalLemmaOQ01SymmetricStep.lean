/-
# Lovász Local Lemma — OQ-01: The Symmetric Form of the Erdős–Lovász Induction Step

`Proofs/LovaszLocalLemmaOQ01InductionStep.lean` verifies the Erdős–Lovász induction step
in its **asymmetric** shape: given a denominator lower bound `d ≤ μ[⋂_{S₁} Aⱼᶜ | ⋂_{S₂} Aⱼᶜ]`
and the asymmetric numeric hypothesis `μ(Aᵢ) ≤ x · d`, the per-event failure probability over
the full survival history stays `≤ x` (`cond_failure_le_x`). There `x` and `d` are the
*per-event* value `xᵢ` and the *per-block* product `∏_{j∈S₁}(1 − xⱼ)` — quantities that vary
with the actual neighbour set `S₁`.

The **symmetric** Lovász Local Lemma — the memorable textbook statement — assigns a single
uniform value `x` to *every* event and bounds each event's dependency degree by a single
constant `d_max`: `Aᵢ` depends on at most `d_max` others. Its numeric hypothesis is therefore
the uniform budget

  `μ(Aᵢ) ≤ x · (1 − x)^{d_max}`,

with the exponent the *degree bound* `d_max`, not the actual neighbour count `|S₁|`. Because
the true neighbour block satisfies `|S₁| ≤ d_max` and `0 ≤ 1 − x ≤ 1`, the uniform product
`∏_{j∈S₁}(1 − x) = (1 − x)^{|S₁|}` is **larger** than `(1 − x)^{d_max}` (fewer factors, each
`≤ 1`), so the uniform budget implies the per-block asymmetric budget `μ(Aᵢ) ≤ x · ∏_{S₁}(1 − x)`.
This file lands that reduction and threads it through the committed asymmetric invariant to
deliver the induction step in the symmetric shape the classic LLL actually maintains.

## Main results

* `prod_const_one_sub` : the uniform neighbour product is a power —
  `∏_{j∈S₁}(1 − x) = (1 − x)^{|S₁|}`.
* `one_sub_pow_le_prod_of_card_le` : the degree-bound reduction —
  if `|S₁| ≤ d` then `(1 − x)^d ≤ ∏_{j∈S₁}(1 − x)` (unconditional in `ℝ≥0∞`).
* `symmetric_budget_le` : the uniform budget implies the per-block budget —
  `μ(Aᵢ) ≤ x · (1 − x)^d` with `|S₁| ≤ d` gives `μ(Aᵢ) ≤ x · ∏_{S₁}(1 − x)`.
* `cond_failure_le_x_symmetric` *(flagship)* : the induction-step invariant in symmetric form —
  under the uniform degree-bounded budget `μ(Aᵢ) ≤ x · (1 − x)^{d}` (`|S₁| ≤ d`), a denominator
  lower bound `∏_{S₁}(1 − x) ≤ μ[⋂_{S₁} Aⱼᶜ | ⋂_{S₂} Aⱼᶜ]`, and independence of `Aᵢ` from its
  non-neighbours, `μ[Aᵢ | (⋂_{S₁} Aⱼᶜ) ∩ (⋂_{S₂} Aⱼᶜ)] ≤ x`.
* `symmetric_x_le_one` : the optimal symmetric assignment `x = (d+1)⁻¹` satisfies `x ≤ 1`,
  so it is admissible in `cond_failure_le_x_symmetric` (its budget `x·(1−x)^d =
  (d+1)⁻¹ (d/(d+1))^d` is the tight threshold `T(d)` of the gallery proof / `EulerThreshold`).

Everything is over an arbitrary `IsProbabilityMeasure`; the denominator lower bound is left
abstract exactly as in `InductionStep` (the recursion instantiating it is the sibling
`DenominatorStep`/`DenominatorRecursion` line of work). This file adds only the elementary
`ℝ≥0∞` order step that turns the *degree-bounded uniform* hypothesis into the *per-block*
hypothesis the committed asymmetric invariant consumes.
-/
import Proofs.LovaszLocalLemmaOQ01InductionStep

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
open LovaszLocalLemmaOQ01InductionStep

namespace LovaszLocalLemmaOQ01SymmetricStep

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The uniform neighbour-survival product is a power of `1 − x`:
`∏_{j∈S₁}(1 − x) = (1 − x)^{|S₁|}`. Immediate from `Finset.prod_const`. -/
theorem prod_const_one_sub (S₁ : Finset ℕ) (x : ℝ≥0∞) :
    (∏ _j ∈ S₁, (1 - x)) = (1 - x) ^ S₁.card := by
  rw [Finset.prod_const]

/-- **Degree-bound reduction.** For a neighbour block `S₁` whose size is bounded by the degree
`d` (`|S₁| ≤ d`), the uniform degree-`d` power is a *lower* bound for the actual neighbour
product:

  `(1 − x)^d ≤ ∏_{j∈S₁}(1 − x)`.

In `ℝ≥0∞` truncated subtraction gives `1 − x ≤ 1` *unconditionally* (`tsub_le_self`), so raising
it to the larger exponent `d ≥ |S₁|` only shrinks it (`pow_le_pow_of_le_one`); rewriting the
product as `(1 − x)^{|S₁|}` closes it. No `x ≤ 1` hypothesis is needed. This is the single order
step that lets the uniform (degree-bounded) LLL budget replace the per-block product budget. -/
theorem one_sub_pow_le_prod_of_card_le {x : ℝ≥0∞} {S₁ : Finset ℕ} {d : ℕ}
    (hcard : S₁.card ≤ d) : (1 - x) ^ d ≤ ∏ _j ∈ S₁, (1 - x) := by
  rw [prod_const_one_sub]
  exact pow_le_pow_of_le_one (zero_le _) tsub_le_self hcard

/-- **The uniform budget implies the per-block budget.** If `μ(Aᵢ) ≤ x · (1 − x)^d` (the
symmetric degree-bounded hypothesis, exponent the degree bound `d`) and the true neighbour
block satisfies `|S₁| ≤ d`, then `μ(Aᵢ) ≤ x · ∏_{j∈S₁}(1 − x)` — the per-block asymmetric
hypothesis consumed by `InductionStep.cond_failure_le_x`. Monotonicity of `x * ·` (`gcongr`)
applied to `one_sub_pow_le_prod_of_card_le`. -/
theorem symmetric_budget_le {x p : ℝ≥0∞} {S₁ : Finset ℕ} {d : ℕ}
    (hcard : S₁.card ≤ d) (hp : p ≤ x * (1 - x) ^ d) :
    p ≤ x * ∏ _j ∈ S₁, (1 - x) := by
  refine hp.trans ?_
  gcongr
  exact one_sub_pow_le_prod_of_card_le hcard

variable {A : ℕ → Set Ω}

/-- **The Erdős–Lovász induction step in symmetric form.**
Let `S₁` be the neighbours and `S₂` the non-neighbours of `Aᵢ`, with `Aᵢ` independent of the
non-neighbour survival block `⋂_{j∈S₂} Aⱼᶜ` (of positive measure). Suppose the neighbour count
is bounded by the degree `d` (`|S₁| ≤ d`), a denominator lower bound
`∏_{j∈S₁}(1 − x) ≤ μ[⋂_{S₁} Aⱼᶜ | ⋂_{S₂} Aⱼᶜ]` is available (nonzero), and the **uniform**
degree-bounded LLL budget holds:

  `μ(Aᵢ) ≤ x · (1 − x)^d`.

Then the per-event failure probability over the full survival history stays below the uniform
value:

  `μ[Aᵢ | (⋂_{S₁} Aⱼᶜ) ∩ (⋂_{S₂} Aⱼᶜ)] ≤ x`.

This is the symmetric-LLL form of the induction invariant: a single value `x` and a single
degree bound `d` control every event, independent of the actual neighbour set. Proof: reduce
the uniform budget to the per-block budget (`symmetric_budget_le`) and feed it to the committed
asymmetric invariant `InductionStep.cond_failure_le_x` with denominator `∏_{S₁}(1 − x)`. -/
theorem cond_failure_le_x_symmetric (hA : ∀ i, MeasurableSet (A i))
    (S₁ S₂ : Finset ℕ) (i : ℕ) (d : ℕ) (hcard : S₁.card ≤ d)
    (hposC : μ (⋂ j ∈ S₂, (A j)ᶜ) ≠ 0)
    (hNC : μ ((⋂ j ∈ S₁, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ)) ≠ 0)
    (hindep : IndepSet (A i) (⋂ j ∈ S₂, (A j)ᶜ) μ)
    {x : ℝ≥0∞}
    (hd : (∏ _j ∈ S₁, (1 - x)) ≤ μ[⋂ j ∈ S₁, (A j)ᶜ | ⋂ j ∈ S₂, (A j)ᶜ])
    (hd0 : (∏ _j ∈ S₁, (1 - x)) ≠ 0)
    (hlll : μ (A i) ≤ x * (1 - x) ^ d) :
    μ[A i | (⋂ j ∈ S₁, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ)] ≤ x :=
  cond_failure_le_x hA S₁ S₂ i hposC hNC hindep hd hd0
    (symmetric_budget_le hcard hlll)

/-- The optimal symmetric assignment `x = (d+1)⁻¹` is admissible (`x ≤ 1`), so
`cond_failure_le_x_symmetric` applies to it. At this `x` the uniform budget
`x · (1 − x)^d = (d+1)⁻¹ · (d/(d+1))^d` is exactly the tight threshold `T(d)` maximizing
`x(1 − x)^d` (see `LovaszLocalLemmaOQ01EulerThreshold`), the value the classic symmetric LLL
admits under `e · p · (d+1) ≤ 1`. -/
theorem symmetric_x_le_one (d : ℕ) : ((d : ℝ≥0∞) + 1)⁻¹ ≤ 1 := by
  rw [ENNReal.inv_le_one]
  exact le_add_self

end LovaszLocalLemmaOQ01SymmetricStep
