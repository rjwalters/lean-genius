/-
# Lovász Local Lemma — OQ-01: Positivity of Subset Survival Histories

The measure-theoretic OQ-01 development has assembled the Erdős–Lovász induction step over
**arbitrary subset histories** (`…DependencySplit.lean`, `…InductionStep.lean`,
`…SymmetricStep.lean`) and the neighbour-block denominator recursion
(`…DenominatorRecursion.lean`). Two of those results —
`cond_iInter_compl_ge_prod` and `cond_failure_le_x_prod` — carry a *side condition* that is
assumed but never discharged:

  `hpos` : every partial survival history is non-null,
           `∀ T ⊆ S, μ ((⋂_{j∈T} Aⱼᶜ) ∩ C) ≠ 0`.

The `…ChainRule.lean` file discharges the analogous condition, but **only over prefix
histories** `⋂_{j<n} Aⱼᶜ` (`hist_pos_of_failure_cond_lt_one`, a `Finset.range` induction),
and with no extra conditioning set `C`. The genuine dependency-graph induction conditions on
the survival of an *unstructured subset* of the events, on top of a fixed non-neighbour block
`C`, so the prefix result cannot supply its `hpos`.

This file discharges the subset-history version. Over an arbitrary `IsProbabilityMeasure`,
for a measurable conditioning set `C` of positive measure, if every per-event conditional
failure probability over every sub-block stays below one,

  `∀ a ∈ S, ∀ T ⊆ S, a ∉ T → μ[A a | (⋂_{j∈T} Aⱼᶜ) ∩ C] < 1`,

then every subset survival history conditioned on `C` is non-null,

  `∀ T ⊆ S, μ ((⋂_{j∈T} Aⱼᶜ) ∩ C) ≠ 0`.

The proof is a `Finset.induction` on `S`: the empty history is `univ ∩ C = C` (`μ C ≠ 0`);
each `insert a s` step splits the survival set as `(A a)ᶜ ∩ ((⋂_{j∈s} Aⱼᶜ) ∩ C)` and
telescopes via `cond_mul_eq_inter`, `μ ((A a)ᶜ ∩ H) = μ[(A a)ᶜ | H] · μ(H)`, where the
survival conditional `μ[(A a)ᶜ | H] = 1 - μ[A a | H]` is strictly positive because the failure
bound at `a` (sub-block `s`) is `< 1`, and `μ(H) ≠ 0` by the induction hypothesis. This is the
subset-history analogue of `ChainRule.hist_pos_of_failure_cond_lt_one`, and it supplies the
`hpos` argument of `DenominatorRecursion.cond_iInter_compl_ge_prod` and
`cond_failure_le_x_prod` directly — one of the two undischarged side conditions of the LLL
strong induction.

## Main results

* `survival_pos_of_failure_lt_one_subset` : the subset-history positivity itself,
  `μ ((⋂_{j∈S} Aⱼᶜ) ∩ C) ≠ 0` from the sub-block failure bounds, by induction on `S`.
* `survival_pos_subset_forall` : the `∀ T ⊆ S` packaging that
  `cond_iInter_compl_ge_prod` / `cond_failure_le_x_prod` consume as their `hpos` hypothesis
  (each `T ⊆ S` inherits the sub-block bounds, so the main lemma applies to it).

Everything is over an arbitrary `IsProbabilityMeasure`; the failure bounds are the only
hypotheses. `0` sorries, `0` axioms.
-/
import Mathlib.Probability.ConditionalProbability

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace LovaszLocalLemmaOQ01SubsetHistoryPos

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {A : ℕ → Set Ω}

/-- **Subset survival histories are non-null under sub-block failure bounds.**
For a measurable conditioning set `C` of positive measure, if every per-event conditional
failure probability over every sub-block of `S` stays strictly below one, then the survival
history of `S` conditioned on `C` is non-null:

  `μ ((⋂_{j∈S} Aⱼᶜ) ∩ C) ≠ 0`.

Proof by `Finset.induction` on `S`. Empty: `⋂_{j∈∅} Aⱼᶜ = univ`, so the set is `C`, non-null
by hypothesis. Step `insert a s` (`a ∉ s`): the survival set factors as
`(A a)ᶜ ∩ ((⋂_{j∈s} Aⱼᶜ) ∩ C)`; writing `H = (⋂_{j∈s} Aⱼᶜ) ∩ C`, the telescoping identity
`cond_mul_eq_inter` gives `μ ((A a)ᶜ ∩ H) = μ[(A a)ᶜ | H] · μ(H)`. The second factor is
non-null by the induction hypothesis (the sub-block bounds restrict from `insert a s` to `s`),
and the first is `1 - μ[A a | H]` (on the positive history `H`, `prob_compl_eq_one_sub`), which
is nonzero because the failure bound at `a` over sub-block `s` is `< 1`. -/
theorem survival_pos_of_failure_lt_one_subset (hA : ∀ i, MeasurableSet (A i))
    {C : Set Ω} (hCmeas : MeasurableSet C) (hCpos : μ C ≠ 0) :
    ∀ S : Finset ℕ,
      (∀ a ∈ S, ∀ T ⊆ S, a ∉ T → μ[A a | (⋂ j ∈ T, (A j)ᶜ) ∩ C] < 1) →
      μ ((⋂ j ∈ S, (A j)ᶜ) ∩ C) ≠ 0 := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro _
      simpa using hCpos
  | @insert a s ha ih =>
      intro hfail
      have hsub : s ⊆ insert a s := Finset.subset_insert a s
      -- restrict the sub-block failure bounds from `insert a s` down to `s`
      have hfail' : ∀ b ∈ s, ∀ T ⊆ s, b ∉ T →
          μ[A b | (⋂ j ∈ T, (A j)ᶜ) ∩ C] < 1 :=
        fun b hb T hT hbT =>
          hfail b (Finset.mem_insert_of_mem hb) T (hT.trans hsub) hbT
      -- history `H = (⋂_{j∈s} Aⱼᶜ) ∩ C` is non-null by the induction hypothesis
      have hHpos : μ ((⋂ j ∈ s, (A j)ᶜ) ∩ C) ≠ 0 := ih hfail'
      have hB : MeasurableSet (⋂ j ∈ s, (A j)ᶜ) :=
        Finset.measurableSet_biInter s (fun j _ => (hA j).compl)
      have hHmeas : MeasurableSet ((⋂ j ∈ s, (A j)ᶜ) ∩ C) := hB.inter hCmeas
      -- the survival conditional at `a` is nonzero: `1 - μ[A a | H]` with `μ[A a | H] < 1`
      have hfa : μ[A a | (⋂ j ∈ s, (A j)ᶜ) ∩ C] < 1 :=
        hfail a (Finset.mem_insert_self a s) s hsub ha
      have hsurv : μ[(A a)ᶜ | (⋂ j ∈ s, (A j)ᶜ) ∩ C] ≠ 0 := by
        haveI : IsProbabilityMeasure (μ[|(⋂ j ∈ s, (A j)ᶜ) ∩ C]) :=
          cond_isProbabilityMeasure hHpos
        rw [prob_compl_eq_one_sub (hA a), Ne, tsub_eq_zero_iff_le, not_le]
        exact hfa
      -- factor the survival set and telescope
      have hsplit : (⋂ j ∈ insert a s, (A j)ᶜ) ∩ C
          = (A a)ᶜ ∩ ((⋂ j ∈ s, (A j)ᶜ) ∩ C) := by
        rw [Finset.set_biInter_insert, Set.inter_assoc]
      rw [hsplit, Set.inter_comm ((A a)ᶜ) ((⋂ j ∈ s, (A j)ᶜ) ∩ C),
        ← cond_mul_eq_inter hHmeas ((A a)ᶜ) μ]
      exact mul_ne_zero hsurv hHpos

/-- **The `∀ T ⊆ S` packaging consumed by the denominator recursion.**
Under the same sub-block failure bounds, *every* subset `T ⊆ S` has a non-null survival
history conditioned on `C`. This is exactly the `hpos` hypothesis of
`DenominatorRecursion.cond_iInter_compl_ge_prod` and `cond_failure_le_x_prod`: each `T ⊆ S`
inherits the sub-block bounds (its sub-blocks are sub-blocks of `S`), so
`survival_pos_of_failure_lt_one_subset` applies to `T`. Supplying this discharges one of the
two undischarged side conditions of the LLL strong induction. -/
theorem survival_pos_subset_forall (hA : ∀ i, MeasurableSet (A i))
    {C : Set Ω} (hCmeas : MeasurableSet C) (hCpos : μ C ≠ 0) (S : Finset ℕ)
    (hfail : ∀ a ∈ S, ∀ T ⊆ S, a ∉ T → μ[A a | (⋂ j ∈ T, (A j)ᶜ) ∩ C] < 1) :
    ∀ T ⊆ S, μ ((⋂ j ∈ T, (A j)ᶜ) ∩ C) ≠ 0 := by
  intro T hT
  exact survival_pos_of_failure_lt_one_subset hA hCmeas hCpos T
    (fun a ha U hU haU => hfail a (hT ha) U (hU.trans hT) haU)

end LovaszLocalLemmaOQ01SubsetHistoryPos
