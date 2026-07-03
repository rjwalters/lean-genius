/-
# Lovász Local Lemma — OQ-01: Assembling the Denominator Recursion (∏(1 − xⱼ) survival bound)

`Proofs/LovaszLocalLemmaOQ01DenominatorStep.lean` proved the **single-neighbour peel**

  `mul_one_sub_le_cond_compl : (1 - x) · l ≤ μ[Aᶜ ∩ B | C]`   from `l ≤ μ[B | C]`, `μ[A | B ∩ C] ≤ x`,

which deflates a neighbour-survival lower bound by a factor `(1 - x)` when one more neighbour
`A = Aₖ` is avoided. Its docstring and the OQ-01 knowledge base flag the **iteration** of that
peel — "a well-founded recursion on `|S₁|`, still to be assembled" — as the missing mechanical
core: the recursion that turns the single peel into the full neighbour-block survival lower bound

  `∏_{j∈S₁} (1 - xⱼ) ≤ μ[⋂_{j∈S₁} Aⱼᶜ | C]`,

which `Proofs/LovaszLocalLemmaOQ01InductionStep.lean` (`cond_failure_le_x`) consumes as its
abstract denominator hypothesis `d ≤ μ[⋂_{S₁} Aⱼᶜ | C]`. This file lands that assembly.

## The recursion

`cond_iInter_compl_ge_prod` is a `Finset.induction` on the neighbour block `S`:

* **Base** `S = ∅`: `⋂_{j∈∅} Aⱼᶜ = univ`, so `μ[univ | C] = 1` (given `μ C ≠ 0`), matching the empty
  product `∏_{∅} = 1`.
* **Step** `insert k s` (`k ∉ s`): `set_biInter_insert` factors the survival set as
  `Aₖᶜ ∩ ⋂_{j∈s} Aⱼᶜ`, `prod_insert` factors the product as `(1 - xₖ)·∏_{s}`, and one application
  of the single peel `mul_one_sub_le_cond_compl` — fed the induction hypothesis
  `∏_{s}(1 - xⱼ) ≤ μ[⋂_{s} Aⱼᶜ | C]` — extends the bound to `insert k s`.

The two side-conditions the peel needs at each step — positivity of the partial survival history
`μ[(⋂_{T} Aⱼᶜ) ∩ C] ≠ 0` and a per-event failure bound `μ[Aₖ | (⋂_{T} Aⱼᶜ) ∩ C] ≤ xₖ` — are carried
as hypotheses quantified over **all** sub-blocks `T ⊆ S`, so the induction hypothesis has exactly
the shape needed at every peel. This is the honest content of the assembly: the recursion is
*mechanical given the per-event bounds*; supplying those bounds is the mutually-recursive
Erdős–Lovász invariant proved (abstractly, one denominator at a time) by
`cond_failure_le_x` — see the capstone `cond_failure_le_x_prod`, which threads the assembled
product bound into that invariant, instantiating the previously-abstract denominator `d` with the
concrete `∏_{j∈S₁}(1 - xⱼ)`.

## Main results

* `cond_iInter_compl_ge_prod` *(flagship)* : the neighbour-block survival lower bound
  `∏_{j∈S}(1 - xⱼ) ≤ μ[⋂_{j∈S} Aⱼᶜ | C]`, by induction on `S`.
* `cond_failure_le_x_prod` : the LLL induction-step invariant `μ[Aᵢ | full history] ≤ xᵢ` with the
  denominator instantiated to `∏_{j∈S₁}(1 - xⱼ)` — the shape the LLL strong induction threads.
-/
import Proofs.LovaszLocalLemmaOQ01InductionStep

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
open LovaszLocalLemmaOQ01DenominatorStep LovaszLocalLemmaOQ01InductionStep

namespace LovaszLocalLemmaOQ01DenominatorRecursion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {A : ℕ → Set Ω} {C : Set Ω} {x : ℕ → ℝ≥0∞}

/-- **The denominator recursion (∏(1 − xⱼ) neighbour-survival lower bound).**
For a finite neighbour block `S`, with

* `hpos`  — every partial survival history is non-null: `μ[(⋂_{j∈T} Aⱼᶜ) ∩ C] ≠ 0` for `T ⊆ S`;
* `hbound` — every per-event failure over a partial history is controlled:
  `μ[Aₖ | (⋂_{j∈T} Aⱼᶜ) ∩ C] ≤ xₖ` for `k ∈ S`, `T ⊆ S`, `k ∉ T`,

the neighbour-block survival probability, conditioned on `C`, is bounded below by the product

  `∏_{j∈S} (1 - xⱼ) ≤ μ[⋂_{j∈S} Aⱼᶜ | C]`.

Proof by `Finset.induction` on `S`, iterating the single-neighbour peel
`LovaszLocalLemmaOQ01DenominatorStep.mul_one_sub_le_cond_compl`. This is the "well-founded recursion
on `|S₁|`, still to be assembled" flagged as the open mechanical core in the `DenominatorStep`
docstring — assembled here. -/
theorem cond_iInter_compl_ge_prod (hA : ∀ i, MeasurableSet (A i)) (hC : MeasurableSet C) :
    ∀ S : Finset ℕ,
      (∀ T ⊆ S, μ ((⋂ j ∈ T, (A j)ᶜ) ∩ C) ≠ 0) →
      (∀ k ∈ S, ∀ T ⊆ S, k ∉ T → μ[A k | (⋂ j ∈ T, (A j)ᶜ) ∩ C] ≤ x k) →
      (∏ j ∈ S, (1 - x j)) ≤ μ[⋂ j ∈ S, (A j)ᶜ | C] := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro hpos _hbound
      have hbi : (⋂ j ∈ (∅ : Finset ℕ), (A j)ᶜ) = Set.univ := by simp
      have hC0 : μ C ≠ 0 := by
        have h := hpos ∅ (Finset.empty_subset _)
        rwa [hbi, Set.univ_inter] at h
      rw [Finset.prod_empty, hbi, cond_apply hC, Set.inter_univ,
        ENNReal.inv_mul_cancel hC0 (measure_ne_top μ C)]
  | @insert a s ha ih =>
      intro hpos hbound
      have hsub : s ⊆ insert a s := Finset.subset_insert a s
      -- restrict the side-conditions from `insert a s` down to `s`, feeding the IH
      have hpos' : ∀ T ⊆ s, μ ((⋂ j ∈ T, (A j)ᶜ) ∩ C) ≠ 0 :=
        fun T hT => hpos T (hT.trans hsub)
      have hbound' : ∀ k ∈ s, ∀ T ⊆ s, k ∉ T →
          μ[A k | (⋂ j ∈ T, (A j)ᶜ) ∩ C] ≤ x k :=
        fun k hk T hT hkT => hbound k (Finset.mem_insert_of_mem hk) T (hT.trans hsub) hkT
      have IH := ih hpos' hbound'
      -- factor product and survival set along `insert a s`
      have hB : MeasurableSet (⋂ j ∈ s, (A j)ᶜ) :=
        Finset.measurableSet_biInter s (fun j _ => (hA j).compl)
      have hBC : μ ((⋂ j ∈ s, (A j)ᶜ) ∩ C) ≠ 0 := hpos s hsub
      have hxa : μ[A a | (⋂ j ∈ s, (A j)ᶜ) ∩ C] ≤ x a :=
        hbound a (Finset.mem_insert_self a s) s hsub ha
      rw [Finset.prod_insert ha, Finset.set_biInter_insert a s (fun j => (A j)ᶜ)]
      exact mul_one_sub_le_cond_compl (hA a) hB hC hBC hxa IH

/-- **LLL induction-step invariant with the concrete `∏(1 − xⱼ)` denominator.**
Threading the assembled denominator bound `cond_iInter_compl_ge_prod` into the abstract
induction-step invariant `LovaszLocalLemmaOQ01InductionStep.cond_failure_le_x` instantiates the
previously-abstract denominator `d` with the concrete neighbour product `∏_{j∈S₁}(1 - xⱼ)`. Under
the asymmetric LLL numeric hypothesis `μ(Aᵢ) ≤ xᵢ · ∏_{j∈S₁}(1 - xⱼ)`, the per-event failure
probability given the full survival history stays below the assigned value:

  `μ[Aᵢ | (⋂_{S₁} Aⱼᶜ) ∩ (⋂_{S₂} Aⱼᶜ)] ≤ xᵢ`.

`S₁` is the neighbour block, `S₂` the non-neighbour block, `hindep` the dependency-graph
independence of `Aᵢ` from its non-neighbours, and `hpos`/`hbound` the per-sub-block side conditions
the denominator recursion consumes (over the non-neighbour history `C = ⋂_{S₂} Aⱼᶜ`). This is the
exact shape the Lovász Local Lemma strong induction maintains at each conditioning event. -/
theorem cond_failure_le_x_prod (hA : ∀ i, MeasurableSet (A i))
    (S₁ S₂ : Finset ℕ) (i : ℕ)
    (hposC : μ (⋂ j ∈ S₂, (A j)ᶜ) ≠ 0)
    (hNC : μ ((⋂ j ∈ S₁, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ)) ≠ 0)
    (hindep : IndepSet (A i) (⋂ j ∈ S₂, (A j)ᶜ) μ)
    (hpos : ∀ T ⊆ S₁, μ ((⋂ j ∈ T, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ)) ≠ 0)
    (hbound : ∀ k ∈ S₁, ∀ T ⊆ S₁, k ∉ T →
      μ[A k | (⋂ j ∈ T, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ)] ≤ x k)
    (hprod0 : (∏ j ∈ S₁, (1 - x j)) ≠ 0)
    (hlll : μ (A i) ≤ x i * ∏ j ∈ S₁, (1 - x j)) :
    μ[A i | (⋂ j ∈ S₁, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ)] ≤ x i := by
  have hC : MeasurableSet (⋂ j ∈ S₂, (A j)ᶜ) :=
    Finset.measurableSet_biInter S₂ (fun j _ => (hA j).compl)
  have hden : (∏ j ∈ S₁, (1 - x j)) ≤ μ[⋂ j ∈ S₁, (A j)ᶜ | ⋂ j ∈ S₂, (A j)ᶜ] :=
    cond_iInter_compl_ge_prod hA hC S₁ hpos hbound
  exact cond_failure_le_x hA S₁ S₂ i hposC hNC hindep hden hprod0 hlll

end LovaszLocalLemmaOQ01DenominatorRecursion
