# Problem: Complete Proof of Erdős Problem #156 — Minimum Size of Maximal Sidon Sets

**Slug**: erdos-156-incomplete-01
**Created**: 2026-04-03T00:52:22-07:00
**Updated**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{Does there exist a maximal Sidon set } A \subset \{1,\ldots,N\} \text{ of size } O(N^{1/3})?
$$

### Plain Language

A **Sidon set** (B₂ set) is a set where all pairwise sums a + b (a ≤ b) are distinct.
A **maximal** Sidon set cannot have any element added while preserving the Sidon property.

Erdős conjectured the minimum size of a maximal Sidon subset of {1,...,N} is Θ(N^{1/3}).
Ruzsa proved the upper bound O(N^{1/3+ε}); the matching lower bound remains open.

### Why This Matters

This is a central problem in additive combinatorics. The exponent α = 1/3 (if true) would
tightly characterize how sparse a maximal Sidon set can be, connecting extremal combinatorics
with additive structure. The gap between trivial lower bound Ω(N^{1/4}) and Ruzsa's O(N^{1/3+ε})
is a longstanding open question.

## Current Lean Status

- **Gallery proof**: `erdos-156` (3 sorries remaining, badge: formalized)
- **Proof file**: `proofs/Proofs/Erdos156Problem.lean`

**Goal**: Identify and fill the 3 sorry statements in the formalized proof.

## Known Results

### What's Already Proven

- Erdős-Turán conjecture bound: any Sidon set in {1,...,N} has size O(N^{1/2})
- Ruzsa's upper bound: there exist maximal Sidon sets in {1,...,N} of size O(N^{1/3+ε})
- `sidon_iff_sidon_alt` — equivalence of Sidon definitions (proven in erdos-157)

### What's Still Open

1. Does the growth exponent α = lim log(minMaximalSidonSize N)/log N exist, and if so, is it exactly 1/3?
2. Can Ruzsa's construction be derandomized or simplified to remove the ε in the exponent?
3. What is the typical size of a random maximal Sidon set in {1,...,N}?
4. How does the problem generalize to B_h sequences for h > 2?
5. Is there a polynomial-time algorithm to find a maximal Sidon set of size O(N^{1/3+ε})?

### Our Goal

Fill the 3 sorry statements in `proofs/Proofs/Erdos156Problem.lean`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-156` | Parent proof (3 sorries) | Sidon sets, counting arguments |
| `erdos-157` | Companion: infinite Sidon sets | Sidon set definitions |

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
  - erdos
  - completion
source: gallery-gap
created: 2026-04-03
```

**Significance**: 8/10
**Tractability**: 5/10
