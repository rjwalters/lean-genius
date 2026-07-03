/-
# Lovász Local Lemma — OQ-01: Assembling the Erdős–Lovász Induction Step

The measure-theoretic OQ-01 development has, in separate files, verified the two *halves*
of the Erdős–Lovász dependency-graph induction step, but never the **ratio that assembles
them into the step's actual conclusion**. This file supplies exactly that assembly.

Recall the induction step. To bound the conditional failure probability of an event `Aᵢ`
given the survival of an arbitrary subset `S` of the other events, one splits
`S = S₁ ⊔ S₂` into the **neighbours** `S₁` and **non-neighbours** `S₂` of `Aᵢ` in the
dependency graph, writes `N = ⋂_{j∈S₁} Aⱼᶜ` (neighbour survival) and `C = ⋂_{j∈S₂} Aⱼᶜ`
(non-neighbour survival), and uses the two-block conditioning identity

  `μ[Aᵢ | N ∩ C] = μ[Aᵢ ∩ N | C] / μ[N | C]`

to reduce the target to a **numerator** over `C` and a **denominator** over `C`:

* **numerator** `μ[Aᵢ ∩ N | C] ≤ μ(Aᵢ)` — the neighbour factor is dropped and the
  non-neighbour history collapses by independence
  (`LovaszLocalLemmaOQ01DependencySplit.cond_failure_le_measure_of_indep_num`);
* **denominator** `μ[N | C] ≥ ∏_{j∈S₁}(1 - xⱼ)` — the neighbour-survival lower bound
  assembled by iterating the peel of
  `LovaszLocalLemmaOQ01DenominatorStep`.

Given a numerator upper bound and a denominator lower bound, the ratio yields the step's
conclusion `μ[Aᵢ | N ∩ C] ≤ μ(Aᵢ) / ∏(1 - xⱼ)`, and under the LLL hypothesis
`μ(Aᵢ) ≤ xᵢ · ∏(1 - xⱼ)` this closes to `μ[Aᵢ | N ∩ C] ≤ xᵢ` — reproducing the induction
*invariant* at one more conditioning event, which is precisely the recursion the LLL
strong induction threads.

This file lands that assembly. It is deliberately abstract in the denominator lower bound
`d ≤ μ[N | C]` (the recursion that instantiates `d = ∏(1 - xⱼ)` from the peel is still the
open combinatorial core; see the sibling `DenominatorStep`/`ConditionalAvoidance` files):
here we verify that *once* a denominator lower bound is available, the ratio combines with
the already-proved numerator half to deliver the induction-step invariant.

## Main results

* `cond_le_div` : abstract ratio bound —
  `μ[A ∩ N | C] ≤ num`, `denom ≤ μ[N | C]`, `denom ≠ 0` ⟹ `μ[A | N ∩ C] ≤ num / denom`.
* `cond_failure_le_measure_div` : the LLL induction step over an arbitrary neighbour /
  non-neighbour split — `μ[Aᵢ | (⋂_{S₁} Aⱼᶜ) ∩ (⋂_{S₂} Aⱼᶜ)] ≤ μ(Aᵢ) / d` from a
  denominator lower bound `d ≤ μ[⋂_{S₁} Aⱼᶜ | ⋂_{S₂} Aⱼᶜ]` and independence of `Aᵢ` from
  the non-neighbour block.
* `cond_failure_le_x` : the closed induction *invariant* — under the asymmetric LLL
  hypothesis `μ(Aᵢ) ≤ x · d`, `μ[Aᵢ | (⋂_{S₁} Aⱼᶜ) ∩ (⋂_{S₂} Aⱼᶜ)] ≤ x`.

Everything is over an arbitrary `IsProbabilityMeasure`; the only independence used is that
of `Aᵢ` from its non-neighbour survival block (supplied as a hypothesis).
-/
import Proofs.LovaszLocalLemmaOQ01DependencySplit
import Proofs.LovaszLocalLemmaOQ01DenominatorStep

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
open LovaszLocalLemmaOQ01DependencySplit LovaszLocalLemmaOQ01DenominatorStep

namespace LovaszLocalLemmaOQ01InductionStep

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Abstract ratio bound (the two-block induction-step combine).**
For events `A N C` over a probability measure with `μ(N ∩ C) ≠ 0`, the two-block
conditioning identity `μ[A ∩ N | C] = μ[A | N ∩ C] · μ[N | C]` turns an upper bound on
the numerator `μ[A ∩ N | C] ≤ num` and a lower bound on the denominator
`denom ≤ μ[N | C]` (with `denom ≠ 0`) into the ratio bound

  `μ[A | N ∩ C] ≤ num / denom`.

This is the exact step the Erdős–Lovász induction performs: instantiate `N` = neighbour
survival, `C` = non-neighbour survival, `num = μ(Aᵢ)`, `denom = ∏(1 - xⱼ)`. Proof:
`cond_inter_eq_cond_cond_mul` gives the identity; monotonicity in the denominator and the
numerator bound give `μ[A | N ∩ C] · denom ≤ num`; `ENNReal.le_div_iff_mul_le` divides
(the denominator is finite, being `≤ μ[N | C] ≠ ∞`, and nonzero by hypothesis). -/
theorem cond_le_div {A N C : Set Ω} (hN : MeasurableSet N) (hC : MeasurableSet C)
    (hNC : μ (N ∩ C) ≠ 0) {num denom : ℝ≥0∞}
    (hnum : μ[A ∩ N | C] ≤ num) (hdenom : denom ≤ μ[N | C]) (hdenom0 : denom ≠ 0) :
    μ[A | N ∩ C] ≤ num / denom := by
  have hdenom_ne : denom ≠ ∞ := ne_top_of_le_ne_top (cond_ne_top hC N) hdenom
  have hkey : μ[A ∩ N | C] = μ[A | N ∩ C] * μ[N | C] :=
    cond_inter_eq_cond_cond_mul hN hC hNC
  have hmul : μ[A | N ∩ C] * denom ≤ num :=
    calc μ[A | N ∩ C] * denom
        ≤ μ[A | N ∩ C] * μ[N | C] := mul_le_mul_left' hdenom _
      _ = μ[A ∩ N | C] := hkey.symm
      _ ≤ num := hnum
  rwa [ENNReal.le_div_iff_mul_le (Or.inl hdenom0) (Or.inl hdenom_ne)]

variable {A : ℕ → Set Ω}

/-- **The Erdős–Lovász induction step over an arbitrary neighbour / non-neighbour split.**
Let `S₁` be the neighbours and `S₂` the non-neighbours of `Aᵢ`, with `Aᵢ` independent of
the non-neighbour survival block `⋂_{j∈S₂} Aⱼᶜ` (of positive measure), and let `d` be any
lower bound for the neighbour-survival conditional `μ[⋂_{S₁} Aⱼᶜ | ⋂_{S₂} Aⱼᶜ]` with
`d ≠ 0`. Then the conditional failure probability of `Aᵢ` given the full survival history
is bounded by the ratio of `μ(Aᵢ)` to the denominator lower bound:

  `μ[Aᵢ | (⋂_{S₁} Aⱼᶜ) ∩ (⋂_{S₂} Aⱼᶜ)] ≤ μ(Aᵢ) / d`.

This assembles the verified numerator half
(`cond_failure_le_measure_of_indep_num`, giving `μ[Aᵢ ∩ (⋂_{S₁} Aⱼᶜ) | ⋂_{S₂} Aⱼᶜ] ≤
μ(Aᵢ)`) with the abstract denominator bound via `cond_le_div`. Only `Aᵢ`'s independence
from its *non-neighbours* is assumed — exactly the dependency-graph structure. -/
theorem cond_failure_le_measure_div (hA : ∀ i, MeasurableSet (A i))
    (S₁ S₂ : Finset ℕ) (i : ℕ)
    (hposC : μ (⋂ j ∈ S₂, (A j)ᶜ) ≠ 0)
    (hNC : μ ((⋂ j ∈ S₁, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ)) ≠ 0)
    (hindep : IndepSet (A i) (⋂ j ∈ S₂, (A j)ᶜ) μ)
    {d : ℝ≥0∞} (hd : d ≤ μ[⋂ j ∈ S₁, (A j)ᶜ | ⋂ j ∈ S₂, (A j)ᶜ]) (hd0 : d ≠ 0) :
    μ[A i | (⋂ j ∈ S₁, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ)] ≤ μ (A i) / d :=
  cond_le_div (measurableSet_survival hA S₁) (measurableSet_survival hA S₂) hNC
    (cond_failure_le_measure_of_indep_num hA S₂ S₁ i hposC hindep) hd hd0

/-- **Closed induction invariant (asymmetric LLL form).**
Under the asymmetric Lovász Local Lemma hypothesis `μ(Aᵢ) ≤ x · d` — where `d` is the
neighbour-survival lower bound `∏_{j∈S₁}(1 - xⱼ)` and `x = xᵢ` the value assigned to
`Aᵢ` — the induction step closes to the *invariant*

  `μ[Aᵢ | (⋂_{S₁} Aⱼᶜ) ∩ (⋂_{S₂} Aⱼᶜ)] ≤ x`.

This is precisely the statement the LLL strong induction maintains at every conditioning
event: the per-event failure probability, conditioned on the survival of any subset of the
other events, never exceeds the assigned value `xᵢ`. Deriving it here from the ratio bound
(`cond_failure_le_measure_div`) and `μ(Aᵢ) ≤ x·d` (via `ENNReal.div_le_iff_le_mul`, the
denominator `d` being finite as a lower bound of the finite conditional and nonzero by
hypothesis) shows the induction step is closed *once the denominator lower bound is
supplied*; the remaining open core is the well-founded recursion that produces that lower
bound `d = ∏(1 - xⱼ)` by iterating the `DenominatorStep` peel. -/
theorem cond_failure_le_x (hA : ∀ i, MeasurableSet (A i))
    (S₁ S₂ : Finset ℕ) (i : ℕ)
    (hposC : μ (⋂ j ∈ S₂, (A j)ᶜ) ≠ 0)
    (hNC : μ ((⋂ j ∈ S₁, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ)) ≠ 0)
    (hindep : IndepSet (A i) (⋂ j ∈ S₂, (A j)ᶜ) μ)
    {x d : ℝ≥0∞}
    (hd : d ≤ μ[⋂ j ∈ S₁, (A j)ᶜ | ⋂ j ∈ S₂, (A j)ᶜ]) (hd0 : d ≠ 0)
    (hlll : μ (A i) ≤ x * d) :
    μ[A i | (⋂ j ∈ S₁, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ)] ≤ x := by
  have hd_ne : d ≠ ∞ :=
    ne_top_of_le_ne_top (cond_ne_top (measurableSet_survival hA S₂) _) hd
  calc μ[A i | (⋂ j ∈ S₁, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ)]
      ≤ μ (A i) / d :=
        cond_failure_le_measure_div hA S₁ S₂ i hposC hNC hindep hd hd0
    _ ≤ x := by rw [ENNReal.div_le_iff_le_mul (Or.inl hd0) (Or.inl hd_ne)]; exact hlll

end LovaszLocalLemmaOQ01InductionStep
