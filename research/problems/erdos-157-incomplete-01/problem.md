# Problem: Complete Proof of Erdős Problem #157 — Infinite Sidon Set as Asymptotic Basis

**Slug**: erdos-157-incomplete-01
**Created**: 2026-04-03T00:52:26-07:00
**Updated**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\exists A \subseteq \mathbb{N}: A \text{ is a Sidon set} \land A \text{ is an asymptotic basis of order 3}
$$

### Plain Language

Does there exist an infinite Sidon set which is also an asymptotic basis of order 3?
(An asymptotic basis of order k means every sufficiently large integer is the sum of at most k elements of A.)

**Answer**: YES — proved by Pilatte (2023). The gallery proof formalizes this with 2 sorries remaining.

### Why This Matters

This resolves a long-standing Erdős question. The Pilatte 2023 result is recent and significant
in additive combinatorics. Completing the Lean formalization would make this a fully verified result.

## Current Lean Status

- **Gallery proof**: `erdos-157` (2 sorries remaining, badge: axiom, status: axiomatized)
- **Proof file**: `proofs/Proofs/Erdos157Problem.lean`
- Two theorems already verified: `sidon_iff_sidon_alt` and `powers_of_two_sidon`

**Goal**: Fill the 2 sorry statements in the formalized proof.

## Known Results

### What's Already Proven (in Lean)

- `sidon_iff_sidon_alt`: Equivalence of Sidon set definitions
- `powers_of_two_sidon`: Powers of two form a Sidon set

### What's Still Open

1. Can an explicit infinite Sidon set that is an order-3 basis be constructed in Lean?
2. What is the smallest order k such that every infinite Sidon set is NOT an order-k basis?
3. Are there natural number-theoretic Sidon sets (like primes of special form) that are order-3 bases?

### Our Goal

Fill the 2 sorry statements in `proofs/Proofs/Erdos157Problem.lean`. Given that Pilatte proved
this in 2023, the mathematical content is settled — the challenge is formalizing the proof.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-157` | Parent proof (2 sorries) | Sidon sets, asymptotic basis |
| `erdos-156` | Companion: maximal Sidon sets | Sidon set definitions |

## Classification

```yaml
tier: A
significance: 8
tractability: 5
tags:
  - seeker-selected
  - combinatorics
  - sidon-sets
  - additive-number-theory
  - asymptotic-basis
  - pilatte-2023
  - erdos
  - completion
source: gallery-gap
created: 2026-04-03
```
