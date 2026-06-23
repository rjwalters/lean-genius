# Problem: PAC Learning and Sample Complexity Bounds

**Slug**: pac-learning-bounds
**Created**: 2026-03-21
**Status**: Active
**Source**: marquee-initiative
**Initiative**: Learning Theory Library (Phase 2)

## Problem Statement

### Formal Statement

$$
\text{VC dimension } d < \infty \iff \text{ PAC learnable}
$$
$$
\text{Sample complexity: } m(\varepsilon, \delta) = O\left(\frac{d + \log(1/\delta)}{\varepsilon^2}\right)
$$

### Plain Language

The PAC (Probably Approximately Correct) framework formalizes what it means for a learning algorithm to generalize from examples. The fundamental theorem of statistical learning says that a concept class is learnable if and only if its VC dimension is finite, and gives tight bounds on how many examples are needed.

### Why This Matters

This would be one of the first formalizations of machine learning theory in any proof assistant. It bridges:
- Combinatorics (Sauer-Shelah lemma, VC dimension)
- Probability theory (uniform convergence, concentration)
- Computer science (learnability, algorithms)

Uniquely differentiated in the Lean ecosystem — almost no one is doing this.

## Dependencies

No hard dependencies on other marquee problems, but benefits from:
- Probability infrastructure from Phase 1 (concentration inequalities)
- Entropy (for information-theoretic learning bounds, optional)

## Known Results

### What's Already in Mathlib

- `Finset` combinatorics for Sauer-Shelah
- Probability concentration inequalities
- Hoeffding/Chernoff bounds may exist

### What Needs to Be Built

- VC dimension definition for set systems
- Sauer-Shelah lemma: |{S ∩ C : C ∈ H}| ≤ Σᵢ₌₀ᵈ C(|S|, i)
- PAC learning framework (concept class, hypothesis class, learner)
- Sample complexity bounds
- Fundamental theorem: finite VC dim ↔ PAC learnable
- Uniform convergence

## Initial Thoughts

### Potential Approaches

1. **Set system approach**: VC dimension on `Set (Set α)` / `Finset (Finset α)`
   - Why it might work: Natural mathematical formulation
   - Risk: Lean type system may make set-of-sets awkward

2. **Function approach**: Hypothesis class as `α → Bool`, VC dim via shattering
   - Why it might work: More CS-flavored, cleaner types
   - Risk: Need to bridge to probability

### Key Difficulties

- Sauer-Shelah lemma (inductive combinatorial argument)
- Uniform convergence over infinite hypothesis classes
- Bridging discrete combinatorics and probability measure

## Tractability Assessment

**Difficulty**: Hard
**Tractability**: 6/10
**Significance**: 9/10

**Justification**:
- Sauer-Shelah is a clean combinatorial result (tractable)
- PAC framework definition is straightforward
- The fundamental theorem requires careful handling of uniform convergence
- Very high novelty value

**Estimated Effort**:
- Exploration: 2 days
- Sauer-Shelah: 2-3 days
- PAC framework: 3-4 days
- Fundamental theorem: 3-5 days

## References

### Papers
- Vapnik & Chervonenkis (1971) - "On the uniform convergence of relative frequencies of events to their probabilities"
- Valiant (1984) - "A theory of the learnable"
- Blumer, Ehrenfeucht, Haussler, Warmuth (1989) - "Learnability and the Vapnik-Chervonenkis dimension"
- Shalev-Shwartz & Ben-David - "Understanding Machine Learning" Ch. 3-6

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Basic`
- `Mathlib.Probability.ProbabilityMassFunction`

## Metadata

```yaml
tags:
  - learning-theory
  - combinatorics
  - probability
  - cs-math-bridge
  - marquee-phase-2
difficulty: hard
source: marquee-initiative
initiative: learning-theory-library
created: 2026-03-21
```
