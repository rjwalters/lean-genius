/-
# Lovász Local Lemma — OQ-01: Closing the Erdős–Lovász Strong Induction

The measure-theoretic OQ-01 development assembled the **single** dependency-graph induction
step — `LovaszLocalLemmaOQ01DenominatorRecursion.cond_failure_le_x_prod` — which bounds the
conditional failure probability of a bad event `Aᵢ` given the survival of a subset `S`,
split into neighbours `S₁` and non-neighbours `S₂`:

  `μ[Aᵢ | (⋂_{S₁} Aⱼᶜ) ∩ (⋂_{S₂} Aⱼᶜ)] ≤ xᵢ`,

**provided** the per-event bound already holds over every *smaller* sub-block
(the `hbound` hypothesis `∀ k ∈ S₁, ∀ T ⊆ S₁, k ∉ T, μ[Aₖ | (⋂_T Aⱼᶜ) ∩ (⋂_{S₂} Aⱼᶜ)] ≤ xₖ`).
Every file in the program flagged the **well-founded recursion that discharges this hypothesis
uniformly in `S`** — "the LLL strong induction" — as the remaining open mechanical core
(see the docstrings of `DenominatorStep`, `DenominatorRecursion`, `SubsetHistoryPos`).

This file lands that recursion. Over the dependency-graph hypotheses of the asymmetric LLL,
a single `Finset.strongInductionOn` on the conditioning set `S` closes the invariant for
**all** `S` at once:

  **`cond_failure_le_x_all` : `∀ i, ∀ S, i ∉ S → μ[Aᵢ | ⋂_{j∈S} Aⱼᶜ] ≤ xᵢ`.**

The induction is clean because *positivity is monotone*: on the branch where the full history
`⋂_{j∈S} Aⱼᶜ` is non-null, every sub-history `⋂_{j∈U} Aⱼᶜ` (`U ⊆ S`) is a superset, hence also
non-null by `measure_mono` — so all of `cond_failure_le_x_prod`'s positivity side-conditions are
free, and its `hbound` hypothesis is supplied verbatim by the strong-induction hypothesis applied
to the strictly smaller conditioning set `T ∪ S₂ ⊂ S`. On the branch where the history is null the
conditional is `0 ≤ xᵢ` trivially.

Feeding the closed invariant into a survival telescope yields the actual Lovász Local Lemma
conclusion over a genuine probability space:

  **`avoidance_pos` : `0 < μ (⋂_{j∈U} Aⱼᶜ)`** for every finite `U` — all bad events avoided with
positive probability.

## Hypotheses (the asymmetric LLL over the dependency relation `dep`)

* `hindep` : each `Aᵢ` is independent of the joint avoidance of any set of its **non-neighbours**
  — `(∀ j ∈ T, ¬ dep i j) → IndepSet (Aᵢ) (⋂_{j∈T} Aⱼᶜ) μ`. This is the dependency-graph
  structure (an event is mutually independent of the events outside its neighbourhood).
* `hx1` : the reserved values satisfy `xᵢ < 1`.
* `hlll` : the asymmetric numeric condition `μ(Aᵢ) ≤ xᵢ · ∏_{j∈S₁}(1 - xⱼ)` for every
  all-neighbour block `S₁` (`∀ j ∈ S₁, dep i j`). This is implied by the textbook single
  condition `μ(Aᵢ) ≤ xᵢ · ∏_{j∈Γ(i)}(1 - xⱼ)`, since the product over a sub-block dominates
  the product over the whole neighbourhood.

Everything is over an arbitrary `IsProbabilityMeasure`. `0` sorries, `0` axioms.
-/
import Proofs.LovaszLocalLemmaOQ01DenominatorRecursion
import Mathlib.Probability.ConditionalProbability

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
open LovaszLocalLemmaOQ01DependencySplit LovaszLocalLemmaOQ01InductionStep
  LovaszLocalLemmaOQ01DenominatorRecursion

namespace LovaszLocalLemmaOQ01StrongInduction

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {A : ℕ → Set Ω} {x : ℕ → ℝ≥0∞}

omit [MeasurableSpace Ω] in
/-- `⋂` over a `Finset` union splits as the intersection of the two `⋂`s. -/
private theorem biInter_finset_union (S T : Finset ℕ) (f : ℕ → Set Ω) :
    (⋂ j ∈ S ∪ T, f j) = (⋂ j ∈ S, f j) ∩ (⋂ j ∈ T, f j) := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩
  · rintro ⟨h1, h2⟩ j (hj | hj)
    · exact h1 j hj
    · exact h2 j hj

omit [IsProbabilityMeasure μ] in
/-- Superset of index ⇒ non-null history: if the survival history of `S` is non-null then so
is that of any subset `U ⊆ S` (a larger set, by `measure_mono`). -/
private theorem hist_mono_nonzero {S U : Finset ℕ} (hUS : U ⊆ S)
    (hSne : μ (⋂ j ∈ S, (A j)ᶜ) ≠ 0) : μ (⋂ j ∈ U, (A j)ᶜ) ≠ 0 := by
  refine fun h => hSne (measure_mono_null ?_ h)
  intro ω hω
  simp only [Set.mem_iInter] at hω ⊢
  exact fun j hj => hω j (hUS hj)

/-- **The closed Erdős–Lovász induction invariant.**
Under the dependency-graph hypotheses of the asymmetric Lovász Local Lemma, the conditional
failure probability of every bad event `Aᵢ`, given the survival of an arbitrary finite set `S`
of other events (`i ∉ S`), never exceeds the reserved value `xᵢ`:

  `μ[Aᵢ | ⋂_{j∈S} Aⱼᶜ] ≤ xᵢ`.

This is the invariant the LLL strong induction maintains at every conditioning event, proved
here for all `S` by a single `Finset.strongInductionOn` on the conditioning set, feeding the
per-step bound `cond_failure_le_x_prod` its `hbound` hypothesis from the strong-induction
hypothesis at the strictly smaller conditioning set `T ∪ S₂ ⊂ S`. -/
theorem cond_failure_le_x_all
    (hA : ∀ i, MeasurableSet (A i))
    (dep : ℕ → ℕ → Prop) [DecidableRel dep]
    (hindep : ∀ (i : ℕ) (T : Finset ℕ), (∀ j ∈ T, ¬ dep i j) →
      IndepSet (A i) (⋂ j ∈ T, (A j)ᶜ) μ)
    (hx1 : ∀ i, x i < 1)
    (hlll : ∀ (i : ℕ) (S₁ : Finset ℕ), (∀ j ∈ S₁, dep i j) →
      μ (A i) ≤ x i * ∏ j ∈ S₁, (1 - x j)) :
    ∀ (S : Finset ℕ) (i : ℕ), i ∉ S → μ[A i | ⋂ j ∈ S, (A j)ᶜ] ≤ x i := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro i _hiS
    rcases eq_or_ne (μ (⋂ j ∈ S, (A j)ᶜ)) 0 with hnull | hSne
    · -- null history: the conditional is `0`
      rw [cond_apply (measurableSet_survival hA S),
        measure_mono_null Set.inter_subset_left hnull, mul_zero]
      exact zero_le _
    · -- positive history: apply the single induction step over the neighbour / non-neighbour split
      set S₁ := S.filter (dep i) with hS1def
      set S₂ := S.filter (fun j => ¬ dep i j) with hS2def
      have hS12 : S₁ ∪ S₂ = S := by
        rw [hS1def, hS2def]; exact Finset.filter_union_filter_neg_eq (p := dep i) S
      have hdisj : Disjoint S₁ S₂ := by
        rw [hS1def, hS2def]; exact Finset.disjoint_filter_filter_neg S S (dep i)
      have hS1sub : S₁ ⊆ S := by rw [hS1def]; exact Finset.filter_subset _ _
      have hS2sub : S₂ ⊆ S := by rw [hS2def]; exact Finset.filter_subset _ _
      have hmemS1 : ∀ j ∈ S₁, dep i j := by
        intro j hj; rw [hS1def] at hj; exact (Finset.mem_filter.1 hj).2
      have hmemS2 : ∀ j ∈ S₂, ¬ dep i j := by
        intro j hj; rw [hS2def] at hj; exact (Finset.mem_filter.1 hj).2
      -- rewrite the goal history along the split
      have hsplit : (⋂ j ∈ S, (A j)ᶜ)
          = (⋂ j ∈ S₁, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ) := by
        rw [← hS12]; exact biInter_finset_union S₁ S₂ (fun j => (A j)ᶜ)
      -- positivity side-conditions, all free by monotonicity
      have hposC : μ (⋂ j ∈ S₂, (A j)ᶜ) ≠ 0 := hist_mono_nonzero hS2sub hSne
      have hNC : μ ((⋂ j ∈ S₁, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ)) ≠ 0 := by
        rw [← biInter_finset_union, hS12]; exact hSne
      have hpos : ∀ T ⊆ S₁, μ ((⋂ j ∈ T, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ)) ≠ 0 := by
        intro T hT
        rw [← biInter_finset_union]
        exact hist_mono_nonzero (Finset.union_subset (hT.trans hS1sub) hS2sub) hSne
      -- independence of `Aᵢ` from its non-neighbours
      have hindep_i : IndepSet (A i) (⋂ j ∈ S₂, (A j)ᶜ) μ := hindep i S₂ hmemS2
      -- the strong-induction hypothesis supplies `hbound` at the smaller block `T ∪ S₂ ⊂ S`
      have hbound : ∀ k ∈ S₁, ∀ T ⊆ S₁, k ∉ T →
          μ[A k | (⋂ j ∈ T, (A j)ᶜ) ∩ (⋂ j ∈ S₂, (A j)ᶜ)] ≤ x k := by
        intro k hkS1 T hT hkT
        have hWS : T ∪ S₂ ⊆ S := Finset.union_subset (hT.trans hS1sub) hS2sub
        have hkS : k ∈ S := hS1sub hkS1
        have hkW : k ∉ T ∪ S₂ := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hkT, fun hk2 => (Finset.disjoint_left.1 hdisj) hkS1 hk2⟩
        have hWss : T ∪ S₂ ⊂ S := (Finset.ssubset_iff_of_subset hWS).2 ⟨k, hkS, hkW⟩
        have hb := ih (T ∪ S₂) hWss k hkW
        rwa [biInter_finset_union] at hb
      -- numeric hypotheses
      have hprod0 : (∏ j ∈ S₁, (1 - x j)) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro j _
        rw [ne_eq, tsub_eq_zero_iff_le, not_le]
        exact hx1 j
      have hlll_i : μ (A i) ≤ x i * ∏ j ∈ S₁, (1 - x j) := hlll i S₁ hmemS1
      rw [hsplit]
      exact cond_failure_le_x_prod hA S₁ S₂ i hposC hNC hindep_i hpos hbound hprod0 hlll_i

/-- **The Lovász Local Lemma over a real probability space (avoidance positivity).**
Under the asymmetric-LLL dependency-graph hypotheses, for every finite set `U` of bad events the
probability that *none* of them occurs is strictly positive:

  `0 < μ (⋂_{j∈U} Aⱼᶜ)`.

Proof: `Finset.induction` on `U`. The empty history is `univ` (mass `1`); each `insert a s` step
telescopes `μ((A a)ᶜ ∩ ⋂_s Aⱼᶜ) = μ[(A a)ᶜ | ⋂_s Aⱼᶜ] · μ(⋂_s Aⱼᶜ)`, whose first factor is
`1 - μ[A a | ⋂_s Aⱼᶜ] ≥ 1 - xₐ > 0` by the closed invariant `cond_failure_le_x_all` and `xₐ < 1`,
and whose second factor is positive by the induction hypothesis. This is the conclusion open
question OQ-01 asks for: the full measure-theoretic Lovász Local Lemma. -/
theorem avoidance_pos
    (hA : ∀ i, MeasurableSet (A i))
    (dep : ℕ → ℕ → Prop) [DecidableRel dep]
    (hindep : ∀ (i : ℕ) (T : Finset ℕ), (∀ j ∈ T, ¬ dep i j) →
      IndepSet (A i) (⋂ j ∈ T, (A j)ᶜ) μ)
    (hx1 : ∀ i, x i < 1)
    (hlll : ∀ (i : ℕ) (S₁ : Finset ℕ), (∀ j ∈ S₁, dep i j) →
      μ (A i) ≤ x i * ∏ j ∈ S₁, (1 - x j))
    (U : Finset ℕ) :
    0 < μ (⋂ j ∈ U, (A j)ᶜ) := by
  have hinv := cond_failure_le_x_all hA dep hindep hx1 hlll
  induction U using Finset.induction_on with
  | empty =>
      have h : (⋂ j ∈ (∅ : Finset ℕ), (A j)ᶜ) = Set.univ := by simp
      rw [h, measure_univ]; exact zero_lt_one
  | @insert a s ha ih =>
      have hsurv : μ (⋂ j ∈ s, (A j)ᶜ) ≠ 0 := ih.ne'
      have hbs : MeasurableSet (⋂ j ∈ s, (A j)ᶜ) := measurableSet_survival hA s
      rw [Finset.set_biInter_insert a s (fun j => (A j)ᶜ), Set.inter_comm,
        ← cond_mul_eq_inter hbs ((A a)ᶜ) μ, pos_iff_ne_zero]
      apply mul_ne_zero
      · haveI : IsProbabilityMeasure (μ[|⋂ j ∈ s, (A j)ᶜ]) :=
          cond_isProbabilityMeasure hsurv
        rw [prob_compl_eq_one_sub (hA a), ne_eq, tsub_eq_zero_iff_le, not_le]
        exact lt_of_le_of_lt (hinv s a ha) (hx1 a)
      · exact hsurv

end LovaszLocalLemmaOQ01StrongInduction
