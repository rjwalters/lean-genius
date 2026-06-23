# Problem: Formalize L'Hôpital's Rule Failure Cases

**Slug**: lhopital-oq-01
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-open-question

## Problem Statement

### Plain Language

Construct a Lean 4 proof showing L'Hôpital's rule can fail: exhibit functions f, g
where lim(f/g) exists but lim(f'/g') does not (or has a different value). The classic
counterexample is f(x) = x + sin x, g(x) = x near ∞.

### Formal Statement

```lean
-- Target theorem in Lean 4 style:
theorem lhopital_failure :
    ∃ (f g : ℝ → ℝ), HasDerivAt f _ _ ∧ HasDerivAt g _ _ ∧
    Filter.Tendsto (fun x => f x / g x) Filter.atTop (nhds 1) ∧
    ¬ Filter.Tendsto (fun x => deriv f x / deriv g x) Filter.atTop (nhds _) := by
  -- Witness: f(x) = x + sin x, g(x) = x
  sorry
```

### Why This Matters

L'Hôpital's rule (Wiedijk #65 area) requires that lim f'/g' exists as a hypothesis.
Formalizing a counterexample clarifies the conditions and is pedagogically valuable.
This extends the existing `LHopital.lean` gallery proof (which proves the rule holds
under its hypotheses) with a complementary "tightness" result.

## Known Results

### What's Already Proven

- `LHopital.lean`: the rule holds when f'/g' has a limit and g' ≠ 0
- `LHopitalOQ02.lean`, `LHopitalOQ03.lean`: extensions in the gallery
- Mathlib has `Filter.Tendsto` and `HasDerivAt` machinery

### Our Goal

Formalize: `¬ ∃ L, Filter.Tendsto (fun x => (1 + cos x) / 1) atTop (nhds L)`, then
combine with `lim (x + sin x) / x = 1` to get the failure counterexample.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| lhopital | Source proof of the rule | Filter.Tendsto, HasDerivAt |

## Initial Thoughts

### Potential Approaches

1. **Direct witness**: Prove `(1 + cos x) / 1` has no limit as x → ∞ by showing it
   oscillates between 0 and 2
   - Key: `cos x` doesn't converge; use `Filter.frequently_iff` to show oscillation

2. **Mathlib search**: Look for `Real.tendsto_cos_atTop` or divergence lemmas for
   oscillating functions in Mathlib

### Key Difficulties

- Formalizing "does not converge" (¬ ∃ L, Tendsto ...) is harder than convergence
- May need `limsup/liminf` divergence condition

## Tractability Assessment

**Difficulty**: Medium — the math is elementary but the Lean formalization of
divergence is not always straightforward.

## Metadata

```yaml
tags:
  - calculus
  - analysis
  - limits
  - wiedijk-100
  - extension
  - counterexample
related_proofs:
  - lhopital
difficulty: medium
source: gallery-open-question
created: 2026-04-21
```

**Significance**: 7/10
**Tractability**: 7/10
