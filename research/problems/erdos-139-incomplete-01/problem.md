# Problem: Complete Proof of Szemerédi's Theorem (Erdős #139)

**Slug**: erdos-139-incomplete-01
**Created**: 2026-04-03T00:52:26-07:00
**Updated**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall k \in \mathbb{N},\ \delta > 0: \exists N_0,\ \forall N > N_0:\ r_k(N) < \delta \cdot N
$$

where r_k(N) is the maximum size of a k-AP-free subset of {1,...,N}.

Equivalently: any subset of natural numbers with positive upper density contains arbitrarily
long arithmetic progressions.

### Plain Language

Szemerédi's theorem (1975) proves that "dense" sets of integers must contain long arithmetic
progressions. This resolved a conjecture of Erdős and Turán from 1936.

The gallery proof formalizes the density formulation but has 1 sorry remaining.

### Why This Matters

Szemerédi's theorem is one of the great results of 20th century combinatorics. Multiple proofs
exist (Szemerédi's combinatorial proof, Furstenberg's ergodic proof, Gowers' Fourier-analytic
proof, Kelley-Meka 2023 quantitative bounds). Completing the Lean formalization with 0 sorries
would be a significant achievement.

## Current Lean Status

- **Gallery proof**: `erdos-139` (1 sorry remaining, badge: axiom, status: axiomatized)
- **Proof file**: `proofs/Proofs/SzemerédiTheorem.lean`

**Goal**: Fill the 1 sorry statement. With only 1 sorry, this may be the most tractable of the
current Tier A incomplete problems.

## Known Results

### What's Already Formalized

- The density reformulation: r_k(N)/N → 0
- Key structural lemmas building toward the proof

### What's Still Open in the Lean Proof

1. The 1 remaining sorry (identify exactly what it covers)
2. Formalize hypergraph regularity lemma for k≥4 (advanced, may need axiom)
3. Connect to Furstenberg's ergodic theory proof
4. Formalize Kelley-Meka 2023 quantitative bounds (very recent, very hard)

### Our Goal

Fill the 1 sorry in `proofs/Proofs/SzemerédiTheorem.lean`. First step: identify what
the sorry covers — if it's a structural lemma, it may be doable.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-139` | Parent proof (1 sorry) | Density, arithmetic progressions |
| `erdos-138` | Companion: Van der Waerden numbers | Ramsey theory |
| `bounded-prime-gaps` | Analytic number theory techniques | Sieve methods |

## Classification

```yaml
tier: A
significance: 9
tractability: 4
tags:
  - seeker-selected
  - combinatorics
  - arithmetic-progressions
  - szemeredi
  - density-ramsey
  - erdos
  - completion
source: gallery-gap
created: 2026-04-03
```
