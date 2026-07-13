# Problem: Lovász Local Lemma (Symmetric and General)

**Slug**: prob-method-lovasz-local
**Created**: 2026-03-21
**Status**: Active
**Source**: marquee-initiative
**Initiative**: Probabilistic Method Library (Phase 1)

## Problem Statement

### Formal Statement

**Symmetric LLL:**
$$
\text{If } \Pr[A_i] \leq p \text{ for all } i, \text{ each } A_i \text{ depends on at most } d \text{ others,}
$$
$$
\text{and } ep(d+1) \leq 1, \text{ then } \Pr\left[\bigcap_i \overline{A_i}\right] > 0.
$$

**General LLL:**
$$
\text{If there exist } x_i \in [0,1) \text{ such that } \Pr[A_i] \leq x_i \prod_{j \in \Gamma(i)} (1 - x_j),
$$
$$
\text{then } \Pr\left[\bigcap_i \overline{A_i}\right] \geq \prod_i (1 - x_i) > 0.
$$

### Plain Language

The Lovász Local Lemma says: if you have many "bad" events, each individually unlikely, and they don't depend on too many others, then it's possible to avoid ALL of them simultaneously. This is far stronger than a union bound and is the crown jewel of the probabilistic method.

### Why This Matters

The LLL is arguably the most important single result in the probabilistic method. It has applications across combinatorics (graph coloring, Ramsey theory, Latin squares), algorithms (Moser-Tardos constructive version), and theoretical CS. Formalizing it in Lean would be a genuine marquee achievement.

## Dependencies

| Direction | Problem | Relationship |
|-----------|---------|-------------|
| **Depends on** | prob-method-expectation | Basic probability framework |
| **Blocks** | prob-method-applications | LLL applications |

## Known Results

### What's Already in Mathlib

- `SimpleGraph` for dependency graphs
- `MeasureTheory.Measure.IsProbabilityMeasure`
- Product measure constructions

### What Needs to Be Built

- Dependency graph formalization (events, mutual independence outside neighborhoods)
- Symmetric LLL statement and proof
- General LLL with x_i assignment
- Key applications (k-SAT, graph coloring)

### Our Goal

Formalize both the symmetric and general forms of the LLL. The symmetric form is simpler; the general form is more powerful and the real mathematical achievement.

## Initial Thoughts

### Potential Approaches

1. **Classical proof via induction on dependency graph**
   - Why it might work: Direct, well-understood
   - Risk: Induction on subsets can be fiddly in Lean

2. **Entropy compression (Moser-Tardos style)**
   - Why it might work: Constructive, elegant
   - Risk: Algorithmically flavored, may need different infrastructure

3. **Lopsided LLL first**
   - Why it might work: More general, same proof difficulty
   - Risk: Additional abstraction overhead

### Key Difficulties

- Formalizing "dependency graph" for probability events
- Mutual independence outside neighborhoods
- Inductive argument over subsets of events
- Product probability space construction

## Tractability Assessment

**Difficulty**: Hard
**Tractability**: 6/10
**Significance**: 9/10

**Justification**:
- The mathematics is well-understood but technically involved
- Dependency graph formalization is nontrivial
- The inductive proof requires careful Lean engineering
- High payoff: this is the signature theorem of the library

**Estimated Effort**:
- Exploration: 2 days
- Implementation: 5-8 days

## References

### Papers
- Erdős & Lovász (1975) - "Problems and results on 3-chromatic hypergraphs"
- Moser & Tardos (2010) - "A constructive proof of the general Lovász Local Lemma"
- Alon & Spencer - "The Probabilistic Method" Ch. 5

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Basic`
- `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`
- `Mathlib.Probability.Independence.Basic`

## Metadata

```yaml
tags:
  - probabilistic-method
  - combinatorics
  - graph-theory
  - marquee-phase-1
related_proofs:
  - ramseys-theorem
  - friendship-theorem
difficulty: hard
source: marquee-initiative
initiative: probabilistic-method-library
created: 2026-03-21
```
