# Problem: Complete Proof of Van der Waerden Numbers Growth Rate (Erdős #138)

**Slug**: erdos-138-incomplete-01
**Created**: 2026-04-03T00:52:26-07:00
**Updated**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{Does } W(k)^{1/k} \to \infty \text{ as } k \to \infty?
$$

where W(k) is the van der Waerden number: the minimum N such that any 2-coloring of {1,...,N}
contains a monochromatic k-term arithmetic progression.

### Plain Language

Erdős #138 asks whether van der Waerden numbers grow faster than exponential — specifically,
whether W(k)^{1/k} → ∞. This remains **open** with a **$500 prize** from Erdős.

Currently known: W(k) > 2^{k/2} (lower bound); W(k) has tower-type upper bounds.

### Why This Matters

Van der Waerden numbers are fundamental in Ramsey theory. The main conjecture would imply
W(k) grows faster than any fixed exponential — currently unknown. The $500 prize reflects
genuine difficulty. Lean formalization of existing bounds is valuable even without solving the conjecture.

## Current Lean Status

- **Gallery proof**: `erdos-138` (5 sorries remaining, badge: axiom, status: axiomatized)
- **Proof file**: `proofs/Proofs/VanDerWaerdenGrowthRate.lean`

**Goal**: Fill some or all of the 5 sorry statements. With 5 sorries this may be challenging;
start with the most tractable ones.

## Known Results

### What's Proven

- Van der Waerden's theorem: W(k) exists for all k (finitary Ramsey theory)
- Lower bounds: W(k) > 2^{k/2} (probabilistic argument)
- Upper bounds: Tower-type bounds via the original van der Waerden proof

### What's Still Open

1. Does W(k)^{1/k} → ∞? (Main conjecture, $500 prize)
2. Does W(k+1)/W(k) → ∞?
3. Does W(k+1) - W(k) → ∞?
4. Does W(k)/2^k → ∞?
5. Can the tower bound be reduced to a simpler function?

### Our Goal

Fill the sorry statements in the formalized proof. Priority: identify which sorries are
about specific bounds vs the main conjecture (which cannot be proved yet).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-138` | Parent proof (5 sorries) | Ramsey theory, arithmetic progressions |
| `erdos-139` | Companion: Szemerédi's theorem | Density Ramsey theory |

## Classification

```yaml
tier: A
significance: 8
tractability: 5
tags:
  - seeker-selected
  - combinatorics
  - ramsey-theory
  - van-der-waerden
  - arithmetic-progressions
  - erdos
  - completion
source: gallery-gap
created: 2026-04-03
```
