# Problem: Shannon Entropy and Basic Properties

**Slug**: shannon-entropy
**Created**: 2026-03-21
**Status**: Active
**Source**: marquee-initiative
**Initiative**: Information Theory Library (Phase 2)

## Problem Statement

### Formal Statement

$$
H(X) = -\sum_{x \in \mathcal{X}} p(x) \log p(x)
$$
$$
H(X,Y) = H(X) + H(Y|X), \quad I(X;Y) = H(X) - H(X|Y) \geq 0
$$

### Plain Language

Shannon entropy measures the information content (or uncertainty) of a random variable. It is the foundation of information theory — the mathematical framework for data compression, communication, and cryptography. Key properties include non-negativity, the chain rule, subadditivity, and the data processing inequality.

### Why This Matters

Information theory is scandalously under-formalized in proof assistants. A clean entropy library in Lean would be:
- Genuinely novel in the Lean ecosystem
- Highly reusable (coding theory, ML theory, cryptography)
- A bridge between pure math and CS applications
- A foundation for Shannon's coding theorems (next steps)

## Dependencies

| Direction | Problem | Relationship |
|-----------|---------|-------------|
| **Blocks** | shannon-source-coding | Source coding needs entropy |
| **Blocks** | shannon-channel-coding | Channel coding needs mutual information |

## Known Results

### What's Already in Mathlib

- `MeasureTheory.Measure.entropy` — may exist in development branches
- `Real.log` — natural logarithm
- `ProbabilityTheory` — basic probability
- `Finset.sum` — finite summation

### What Needs to Be Built

- Shannon entropy definition for finite distributions
- Conditional entropy H(X|Y)
- Mutual information I(X;Y) = H(X) + H(Y) - H(X,Y)
- Joint entropy H(X,Y)
- Key properties: non-negativity, maximum entropy (uniform), chain rule
- Gibbs inequality (H(p) ≤ H(p,q) + D(p||q))
- Data processing inequality
- Log-sum inequality (key technical lemma)

## Initial Thoughts

### Potential Approaches

1. **Finite distribution approach**: Define on `Finsupp` or `PMF` over finite types
   - Why it might work: Clean, avoids measure theory complexity
   - Risk: Doesn't generalize to continuous entropy

2. **Measure-theoretic approach**: Full generality from the start
   - Why it might work: Maximum reusability, connects to Mathlib infrastructure
   - Risk: Much harder to get right, may already be in development

3. **PMF-based**: Use `MeasureTheory.PMF` as the base
   - Why it might work: Natural fit, already in Mathlib
   - Risk: Need to check how well it composes

### Key Difficulties

- Convention: log base 2 vs natural log (information bits vs nats)
- Handling 0 log 0 = 0 convention
- Joint distributions and marginals in Lean type system
- Making definitions ergonomic for downstream proofs

## Tractability Assessment

**Difficulty**: Medium
**Tractability**: 8/10
**Significance**: 9/10

**Justification**:
- The mathematics is well-understood and elementary
- Mathlib has the prerequisite infrastructure
- Main challenge is API design
- High novelty: very little information theory in Lean

**Estimated Effort**:
- Exploration: 1 day
- Implementation: 3-4 days

## References

### Papers
- Shannon (1948) - "A Mathematical Theory of Communication"
- Cover & Thomas - "Elements of Information Theory" Ch. 2

### Mathlib
- `Mathlib.Probability.ProbabilityMassFunction`
- `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- `Mathlib.MeasureTheory.Measure.MeasureSpace`

## Metadata

```yaml
tags:
  - information-theory
  - analysis
  - probability
  - cs-math-bridge
  - marquee-phase-2
difficulty: medium
source: marquee-initiative
initiative: information-theory-library
created: 2026-03-21
```
