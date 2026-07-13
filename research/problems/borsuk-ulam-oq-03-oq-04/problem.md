# Problem: Formalize quantitative IVT bounds for effective estimates on antipodal pair locations

## Statement

### Plain Language
The 1D Borsuk-Ulam theorem guarantees that any continuous f: [-1,1] → ℝ has an antipodal pair
x₀ with f(x₀) = f(-x₀), proved via IVT on g(x) = f(x) - f(-x). The open question is:
can we give **quantitative bounds** on where x₀ lies, given a modulus of continuity for f?

For instance, if f is L-Lipschitz and |g(1)| = δ > 0, can we prove the antipodal pair lies
in a specific interval away from the boundary, or bound the measure of the set of antipodal pairs?

### Formal Statement
```lean
-- Target: Quantitative 1D Borsuk-Ulam
-- If f: [-1,1] → ℝ is L-Lipschitz and g(x) := f(x) - f(-x),
-- then the zero of g is bounded away from the endpoints proportional to |g(1)|/L.

theorem quantitative_borsuk_ulam_1d
    (f : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hf : LipschitzWith (NNReal.ofReal L) (fun x => f x))
    (hf_cont : ContinuousOn f (Set.Icc (-1) 1))
    (δ : ℝ) (hδ : 0 < δ) (hg : |f 1 - f (-1)| = δ) :
    ∃ x₀ ∈ Set.Icc (-1 + δ / (2 * L)) (1 - δ / (2 * L)),
      f x₀ = f (-x₀) := by
  sorry
```

## Classification

```yaml
tier: B
significance: 7
tractability: 6
tags:
  - topology
  - constructive-math
  - borsuk-ulam
  - ivt
  - antipodal
  - quantitative
  - lipschitz
```

**Significance**: 7/10 — Quantitative versions of topological fixed-point results are useful for
constructive mathematics and computational topology.

**Tractability**: 6/10 — Depends on quantitative IVT in Mathlib; the parent proof infrastructure
in `BorsukUlamOQ03.lean` provides a good foundation.

## Why This Matters

1. **Effective/constructive topology**: Standard BU gives existence with no bound on where the
   antipodal pair is. A quantitative version gives a computable estimate.
2. **Modulus of continuity framework**: Connects to constructive analysis — provides a
   computational certificate for the antipodal pair.
3. **Lean infrastructure**: Tests whether Mathlib's Lipschitz/IVT machinery can support
   quantitative topological arguments.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| borsuk-ulam-oq-03 | Parent: 1D BU via IVT, axiom reduction chain, 5139 lines |
| borsuk-ulam-oq-03-oq-01 | Sibling: related constructive extension |
| borsuk-ulam-oq-03-oq-03 | Sibling: 2D Tucker's lemma, discrete approach |
| intermediate-value-theorem | Core tool: `intermediate_value_Icc` |

## Parent Open Question

From `borsuk-ulam-oq-03` conclusion.openQuestions:
> "Can the quantitative IVT bounds give effective estimates for the location of antipodal pairs?"

## Key Mathlib Theorems to Explore

- `intermediate_value_Icc`: standard IVT
- `LipschitzWith.dist_le_mul`: Lipschitz bound on function values
- `IsConnected.intermediate_value₂`: connectedness-based IVT variant
- `Real.exists_zero`: existence of zeros for sign-changing functions
