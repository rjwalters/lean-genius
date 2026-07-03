/-
# Lovász Local Lemma — OQ-01: The Denominator Recursion Step (Neighbour-Survival Peel)

`Proofs/LovaszLocalLemmaOQ01DependencySplit.lean` supplies the *numerator* moves of the
Erdős–Lovász dependency-graph induction step over an arbitrary subset history — numerator
monotonicity of conditional probability and the non-neighbour independence collapse —
reaching `μ[Aᵢ ∩ (⋂_{S₁} Aⱼᶜ) | ⋂_{S₂} Aⱼᶜ] ≤ μ(Aᵢ)`. That is only the numerator; the
Erdős–Lovász argument bounds `μ[Aᵢ | history]` over the **full** survival
`(⋂_{S₁} Aⱼᶜ) ∩ (⋂_{S₂} Aⱼᶜ)`, for which the missing ingredient is the **neighbour-block
survival lower bound**

  `μ[⋂_{j∈S₁} Aⱼᶜ | C] ≥ ∏_{j∈S₁} (1 - xⱼ)`,

"which the LLL strong induction supplies". That strong induction is a recursion on the
neighbour block `S₁`, peeling one neighbour `Aₖ` at a time. The engine of that
recursion — the single-peel transition that turns a survival lower bound over `S₁ \ {k}`
into one over `S₁` — is missing from every OQ-01 file. This file supplies it.

The transition is the *complement* companion of the conditional chain rule. Where the
chain rule factors a numerator `μ[(A ∩ B) | C] = μ[A | B ∩ C]·μ[B | C]`, the survival
recursion needs the **complement** `μ[Aᶜ ∩ B | C]` — the probability that, on top of
surviving the already-peeled block `B`, the new neighbour `Aₖ` is *also* avoided. Writing
`A = Aₖ`, `B = ⋂_{j∈S₁∖{k}} Aⱼᶜ` (the partially-peeled neighbour survival), `C` the
non-neighbour block, the identity is

  `μ[A ∩ B | C] + μ[Aᶜ ∩ B | C] = μ[B | C]`      (`cond_compl_inter_add`, additive),

and, combined with the numerator factoring `μ[A ∩ B | C] = μ[A | B ∩ C]·μ[B|C]` and a
per-event failure bound `μ[A | B ∩ C] ≤ x`, it yields the multiplicative peel

  `(1 - x) · μ[B | C] ≤ μ[Aᶜ ∩ B | C]`           (`one_sub_mul_cond_le_cond_compl`),

i.e. adding one more avoided neighbour deflates the survival probability by at most a
factor `(1 - x)`. Chaining it against an inductive lower bound `l ≤ μ[B | C]` gives the
recursion step in the exact `∏(1 - xⱼ)` shape:

  `(1 - x) · l ≤ μ[Aᶜ ∩ B | C]`                  (`mul_one_sub_le_cond_compl`).

Iterating this over the neighbours of `Aₖ` (a well-founded recursion on `|S₁|`, still to
be assembled) produces the survival lower bound the dependency split consumes.

Everything is over an arbitrary `IsProbabilityMeasure`, stated abstractly for events
`A B C : Set Ω` (instantiate `A = Aₖ`, `B = ⋂_{S₁∖{k}} Aⱼᶜ`, `C = ⋂_{S₂} Aⱼᶜ`). No
independence is assumed: this is the pure conditional-measure bookkeeping of the peel.
The one numerator identity it uses (`cond_inter_eq_cond_cond_mul`) is reproved inline so
the file depends only on Mathlib.

## Main results

* `cond_ne_top` : `μ[t | s] ≠ ∞` for measurable `s` — conditionals are finite (needed to
  cancel/subtract them; not packaged in Mathlib for a general conditioning set).
* `cond_compl_inter_add` : `μ[A ∩ B | C] + μ[Aᶜ ∩ B | C] = μ[B | C]` — the additive peel
  identity (the survival mass over `B` splits according to whether `A` also holds).
* `one_sub_mul_cond_le_cond_compl` *(flagship)* : `(1 - x) · μ[B | C] ≤ μ[Aᶜ ∩ B | C]`
  from `μ[A | B ∩ C] ≤ x` — the multiplicative single-neighbour peel.
* `mul_one_sub_le_cond_compl` : `(1 - x) · l ≤ μ[Aᶜ ∩ B | C]` from a survival lower bound
  `l ≤ μ[B | C]` — the recursion step in `∏(1 - xⱼ)` form.
-/
import Mathlib.Probability.ConditionalProbability

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LovaszLocalLemmaOQ01DenominatorStep

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {A B C : Set Ω}

/-- **Two-block conditioning chain rule (numerator identity).**
`μ[(A ∩ B) | C] = μ[A | B ∩ C] · μ[B | C]`, for arbitrary events over a probability
measure with `μ(B ∩ C) ≠ 0`. Reproved inline (it also appears in the sibling BayesSplit
development) so this file depends only on Mathlib. Proof: `cond_apply` unfolds all three
conditionals to `(measure)⁻¹ · (intersection measure)`; the `μ(B ∩ C)` factor cancels
against its inverse (finite, nonzero over a probability measure) and the surviving
intersections agree after reassociation. -/
theorem cond_inter_eq_cond_cond_mul (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : μ (B ∩ C) ≠ 0) :
    μ[(A ∩ B) | C] = μ[A | B ∩ C] * μ[B | C] := by
  rw [cond_apply hC, cond_apply (hB.inter hC), cond_apply hC]
  have e2 : μ (B ∩ C ∩ A) = μ (C ∩ (A ∩ B)) := by
    congr 1
    ext x; simp only [Set.mem_inter_iff]; tauto
  have e1 : μ (C ∩ B) = μ (B ∩ C) := by rw [Set.inter_comm]
  rw [e1, e2,
    show (μ (B ∩ C))⁻¹ * μ (C ∩ (A ∩ B)) * ((μ C)⁻¹ * μ (B ∩ C))
        = ((μ (B ∩ C))⁻¹ * μ (B ∩ C)) * ((μ C)⁻¹ * μ (C ∩ (A ∩ B))) from by ring,
    ENNReal.inv_mul_cancel hBC (measure_ne_top μ _), one_mul]

/-- **Conditionals are finite.**
For any measurable conditioning set `s`, the conditional probability `μ[t | s]` is never
`∞`. If `μ s = 0` the conditional is `0` (the numerator `μ(s ∩ t) ≤ μ s` vanishes); else
`(μ s)⁻¹` and `μ(s ∩ t)` are both finite. Mathlib packages finiteness of `cond` only via
an `IsProbabilityMeasure` instance that requires `μ s ∉ {0, ∞}`; this unconditional
`≠ ∞` fact is what lets the survival peel subtract and cancel conditional masses. -/
theorem cond_ne_top {s : Set Ω} (hs : MeasurableSet s) (t : Set Ω) :
    μ[t | s] ≠ ∞ := by
  rw [cond_apply hs]
  rcases eq_or_ne (μ s) 0 with h | h
  · have h0 : μ (s ∩ t) = 0 := measure_mono_null Set.inter_subset_left h
    rw [h0, mul_zero]; exact ENNReal.zero_ne_top
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 h) (measure_ne_top μ _)

omit [IsProbabilityMeasure μ] in
/-- **Additive peel identity.**
The survival mass over `B`, conditioned on `C`, splits according to whether the new event
`A` also holds:

  `μ[A ∩ B | C] + μ[Aᶜ ∩ B | C] = μ[B | C]`.

This is `measure_inter_add_diff` applied to the conditional measure `cond μ C`, with
`B \ A = Aᶜ ∩ B`. It is the complement companion of the numerator chain rule: where the
chain rule factors `μ[A ∩ B | C]`, the survival recursion needs the residual
`μ[Aᶜ ∩ B | C]` — the mass surviving `B` *and* avoiding `A`. -/
theorem cond_compl_inter_add (hA : MeasurableSet A) :
    μ[A ∩ B | C] + μ[Aᶜ ∩ B | C] = μ[B | C] := by
  have h := measure_inter_add_diff (μ := cond μ C) B hA
  rw [Set.inter_comm B A, Set.diff_eq, Set.inter_comm B Aᶜ] at h
  exact h

/-- **Multiplicative single-neighbour peel (flagship).**
If the per-event failure probability over the refined history `B ∩ C` is bounded,
`μ[A | B ∩ C] ≤ x`, then avoiding `A` on top of surviving `B` deflates the survival
probability by at most the factor `(1 - x)`:

  `(1 - x) · μ[B | C] ≤ μ[Aᶜ ∩ B | C]`.

This is the exact transition the Erdős–Lovász survival recursion performs when it peels
one neighbour `A = Aₖ` off the neighbour block. Proof: the additive peel gives
`μ[Aᶜ ∩ B | C] = μ[B|C] - μ[A ∩ B | C]`; the numerator identity rewrites
`μ[A ∩ B | C] = μ[A | B ∩ C]·μ[B | C]`, at most `x·μ[B|C]`; and `(1 - x)·μ[B|C] =
μ[B|C] - x·μ[B|C]` (`ENNReal.sub_mul`, valid since `μ[B|C] ≠ ∞`). Only the conditioning
set `B ∩ C` needs positive measure (for the numerator identity); no independence. -/
theorem one_sub_mul_cond_le_cond_compl (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hBC : μ (B ∩ C) ≠ 0) {x : ℝ≥0∞} (hx : μ[A | B ∩ C] ≤ x) :
    (1 - x) * μ[B | C] ≤ μ[Aᶜ ∩ B | C] := by
  have ha_ne : μ[B | C] ≠ ∞ := cond_ne_top hC B
  have hp_ne : μ[A | B ∩ C] ≠ ∞ := cond_ne_top (hB.inter hC) A
  -- additive peel, with the numerator factored by the chain rule
  have hadd : μ[A | B ∩ C] * μ[B | C] + μ[Aᶜ ∩ B | C] = μ[B | C] := by
    rw [← cond_inter_eq_cond_cond_mul hB hC hBC]; exact cond_compl_inter_add hA
  -- so the residual equals the truncated subtraction
  have hres : μ[Aᶜ ∩ B | C] = μ[B | C] - μ[A | B ∩ C] * μ[B | C] :=
    ENNReal.eq_sub_of_add_eq (ENNReal.mul_ne_top hp_ne ha_ne)
      (by rw [add_comm]; exact hadd)
  calc (1 - x) * μ[B | C]
      = μ[B | C] - x * μ[B | C] := by rw [ENNReal.sub_mul (fun _ _ => ha_ne), one_mul]
    _ ≤ μ[B | C] - μ[A | B ∩ C] * μ[B | C] :=
        tsub_le_tsub_left (mul_le_mul_right' hx _) _
    _ = μ[Aᶜ ∩ B | C] := hres.symm

/-- **Survival recursion step (∏(1 - xⱼ) form).**
Chaining the multiplicative peel against an inductive survival lower bound `l ≤ μ[B | C]`
gives the recursion step in the shape the Lovász Local Lemma strong induction iterates:

  `(1 - x) · l ≤ μ[Aᶜ ∩ B | C]`.

With `l = ∏_{j∈S₁∖{k}} (1 - xⱼ)` the survival bound over the partially-peeled neighbour
block and `x = xₖ`, one application extends it to `∏_{j∈S₁} (1 - xⱼ)` over the block with
`Aₖ` peeled. Iterating over all neighbours yields the survival lower bound the
dependency-graph induction step consumes. -/
theorem mul_one_sub_le_cond_compl (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hBC : μ (B ∩ C) ≠ 0) {x l : ℝ≥0∞}
    (hx : μ[A | B ∩ C] ≤ x) (hl : l ≤ μ[B | C]) :
    (1 - x) * l ≤ μ[Aᶜ ∩ B | C] :=
  le_trans (mul_le_mul_left' hl _)
    (one_sub_mul_cond_le_cond_compl hA hB hC hBC hx)

end LovaszLocalLemmaOQ01DenominatorStep
