# Problem: First Moment / Expectation Method

**Slug**: prob-method-expectation
**Created**: 2026-03-21
**Status**: Active
**Source**: marquee-initiative
**Initiative**: Probabilistic Method Library (Phase 1)

## Problem Statement

### Formal Statement

$$
\text{If } X \text{ is a random variable on a finite probability space with } \mathbb{E}[X] > 0,
$$
$$
\text{then } \exists \omega : X(\omega) > 0. \text{ (Similarly for } \mathbb{E}[X] < t.)
$$

### Plain Language

The expectation method (first moment method) is the simplest and most fundamental tool in the probabilistic method: if the expected value of a random variable exceeds a threshold, then some outcome must exceed that threshold. Despite its simplicity, it yields powerful existence proofs in combinatorics.

### Why This Matters

This is the foundation of the entire probabilistic method library. Every subsequent technique (alteration, second moment, LLL) builds on expectation arguments. Formalizing this cleanly enables the full library. The canonical application — Erdős's 1947 proof that R(k,k) ≥ 2^(k/2) — would be an immediate payoff.

## Known Results

### What's Already in Mathlib

- `MeasureTheory.integral_pos_of_pos_of_support` — positive integral from positive function
- `Finset.sum_pos` — positive sum from positive summands
- `ProbabilityTheory` — basic probability definitions
- `MeasureTheory.Measure.IsProbabilityMeasure` — probability measure typeclass

### What Needs to Be Built

- Finite probability space combinatorial framework (random subsets, random colorings)
- Linearity of expectation in combinatorial setting (Finset averages)
- First moment method as reusable tactic/lemma pattern
- Application: R(k,k) ≥ 2^(k/2)

### Our Goal

Build the expectation method as reusable infrastructure and prove the Erdős 1947 Ramsey bound as the first application.

## Dependencies

| Direction | Problem | Relationship |
|-----------|---------|-------------|
| **Blocks** | prob-method-alteration | Alteration extends expectation |
| **Blocks** | prob-method-second-moment | Second moment refines first moment |
| **Blocks** | prob-method-lovasz-local | LLL uses expectation arguments |
| **Blocks** | prob-method-applications | Applications need full library |

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| ramseys-theorem | R(k,k) bound is canonical application | Graph coloring, counting |
| birthday-problem | Probability on finite sets | Combinatorial probability |

## Initial Thoughts

### Potential Approaches

1. **Finset.average framework**: Define expectation as average over finite set of outcomes
   - Why it might work: Clean, elementary, avoids measure theory overhead
   - Risk: May not compose well with Mathlib's measure-theoretic probability

2. **MeasureTheory integration**: Use full measure-theoretic expectation
   - Why it might work: Composes with all of Mathlib's probability theory
   - Risk: Overhead for purely combinatorial arguments

3. **Hybrid**: Finset framework for combinatorics, bridge lemma to MeasureTheory
   - Why it might work: Best of both worlds
   - Risk: Bridge lemma may be nontrivial

### Key Difficulties

- Choosing the right abstraction level (finite vs measure-theoretic)
- Making the framework reusable across graph coloring, subset selection, etc.
- Formalizing "random subset of [n]" and "random 2-coloring" cleanly

### What Would a Proof Need?

- Random variable definition on finite combinatorial objects
- Linearity of expectation
- First moment principle: E[X] > t → ∃ω, X(ω) > t
- Application to random graph coloring for Ramsey bound

## Tractability Assessment

**Difficulty**: Medium
**Tractability**: 8/10
**Significance**: 9/10

**Justification**:
- Core mathematical content is elementary
- Mathlib has good probability infrastructure
- Main challenge is API design for reusability

**Estimated Effort**:
- Exploration: 1 day
- Implementation: 2-3 days

## References

### Papers
- Erdős (1947) - "Some remarks on the theory of graphs" (R(k,k) bound)
- Alon & Spencer - "The Probabilistic Method" Ch. 1-2

### Mathlib
- `Mathlib.Probability.ProbabilityMassFunction` — PMF definitions
- `Mathlib.MeasureTheory.Measure.MeasureSpace` — measure spaces
- `Mathlib.Combinatorics.SimpleGraph.Basic` — graph definitions

## Metadata

```yaml
tags:
  - probabilistic-method
  - combinatorics
  - analysis
  - marquee-phase-1
related_proofs:
  - ramseys-theorem
  - birthday-problem
difficulty: medium
source: marquee-initiative
initiative: probabilistic-method-library
created: 2026-03-21
```
