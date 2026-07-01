# Problem: The First-Moment Principle — Some Outcome Meets the Average

**Slug**: prob-method-expectation-oq-05
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: prob-method-expectation

## Problem Statement

### Formal Statement

For a finite nonempty index set `s` and `f : ι → ℝ`,

$$
\exists\, i \in s,\ \frac{1}{|s|}\sum_{j \in s} f(j) \le f(i)
\qquad\text{and}\qquad
\exists\, j \in s,\ f(j) \le \frac{1}{|s|}\sum_{j \in s} f(j).
$$

Equivalently (integral form): if `X` is integrable, then `∃ ω, X ω ≥ 𝔼[X]` and
`∃ ω, X ω ≤ 𝔼[X]`.

### Plain Language

The parent `prob-method-expectation` develops linearity of expectation and its use in the
probabilistic method. The **first-moment principle** is the engine underneath: *some outcome
is at least as good as the average, and some outcome is at most the average.* This is what
lets a probabilistic argument conclude "an object with property P exists" from "the expected
number of P-objects is positive." This child states and proves the principle in both the
finite-average and the integral (expectation) forms.

### Why This Matters

This is the single most-used deduction in the probabilistic method, yet it is usually left
implicit. Mathlib has the finite building blocks (`Finset.exists_le_of_sum_le`,
`Finset.card_nsmul_le_sum`) and the measure-theoretic pair (`MeasureTheory.exists_le_integral`,
`exists_integral_le`), but not a clean, citable "∃ outcome ≥ mean" statement. This child packages
it as a reusable lemma with both faces.

## Known Results

### What's Already Proven

- Parent `prob-method-expectation` is verified (0-axiom).
- Mathlib: `Finset.exists_le_of_sum_le (hs : s.Nonempty) (h : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i) :
  ∃ i ∈ s, f i ≤ g i`; `Finset.card_nsmul_le_sum (h : ∀ x ∈ s, a ≤ f x) : #s • a ≤ ∑ i ∈ s, f i`;
  `MeasureTheory.exists_le_integral (hf : Integrable f μ) : ∃ x, f x ≤ ∫ a, f a ∂μ`;
  `MeasureTheory.exists_integral_le`.

### What's Still Open

- The packaged first-moment statements below (currently `sorry`). No single Mathlib lemma
  states "∃ element ≥ average."

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**principle / completion**.

## Target Lean Sketch

```lean
open Finset

/-- Some element attains at least the average value (finite form). -/
theorem exists_ge_average {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    ∃ i ∈ s, (∑ j ∈ s, f j) ≤ s.card • f i := by
  -- Apply `exists_le_of_sum_le` with `g := fun _ => (∑ j ∈ s, f j)` scaled appropriately,
  -- or: by_contra ⟹ f i < average for all i ⟹ ∑ f < #s • average = ∑ f (card_nsmul_le_sum).
  sorry

/-- Dual: some element is at most the average. -/
theorem exists_le_average {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    ∃ i ∈ s, s.card • f i ≤ (∑ j ∈ s, f j) := by
  sorry

/-- Expectation form (probabilistic method): an outcome beats the mean. -/
theorem exists_ge_expectation {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}
    {X : α → ℝ} (hX : MeasureTheory.Integrable X μ) : ∃ ω, ∫ a, X a ∂μ ≤ X ω := by
  exact MeasureTheory.exists_le_integral hX
```

Add worked `example`s: a finite `f` on `{0,1,2}` with values `1,4,7` — the average is `4`
and index `2` beats it; a Bernoulli-style random variable whose positive expectation forces a
successful outcome.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `prob-method-expectation` | Parent: linearity of expectation | probabilistic method |
| `prob-method-first-moment` (if present) | First-moment method applications | expectation bounds |
| `randomized-maxcut` | Uses "≥ expectation" existence | probabilistic method |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 6/10  |  **Tractability**: 9/10  |  **Tier**: B

**Justification**: The finite forms are one `by_contra` + `card_nsmul_le_sum`, or a direct
`exists_le_of_sum_le` with a constant comparison function. The expectation form is a direct
application of `MeasureTheory.exists_le_integral`. No new machinery.

### Suggested First Steps

1. Prove `exists_ge_average` via `Finset.exists_le_of_sum_le` with `g := const (∑ f)` and
   `f := fun i => s.card • f i`, using `Finset.sum_const` to match totals.
2. Prove the dual by swapping the comparison direction.
3. Discharge the expectation form directly from `MeasureTheory.exists_le_integral`; add the
   worked finite and Bernoulli examples.

## References

### Mathlib

- `Finset.exists_le_of_sum_le`, `Finset.exists_lt_of_sum_lt` — Algebra/Order/BigOperators/Group/Finset.lean
- `Finset.card_nsmul_le_sum` — Algebra/Order/BigOperators/Group/Finset.lean
- `MeasureTheory.exists_le_integral`, `MeasureTheory.exists_integral_le` — MeasureTheory/Integral/Average.lean

### Literature

- Alon & Spencer, *The Probabilistic Method* — the first-moment / averaging principle.

## Metadata

```yaml
tags:
  - probability
  - probabilistic-method
  - expectation
  - averaging
related_proofs:
  - prob-method-expectation
  - randomized-maxcut
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
