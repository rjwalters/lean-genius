# Problem: Rabin-Shallit Algorithm for Four-Square Representations

**Slug**: lagrange-four-squares-oq-01
**Created**: 2026-03-30
**Status**: Active
**Source**: gallery-gap (open question from lagrange-four-squares proof)

## Problem Statement

### Formal Statement

Formalize the Rabin-Shallit (1986) randomized algorithm computing $n = a^2 + b^2 + c^2 + d^2$ in expected $O(\log^2 n)$ time using modular square root extraction.

### Plain Language

Lagrange's theorem guarantees every natural number is a sum of four squares, but doesn't say how to find them. The Rabin-Shallit algorithm does this efficiently. Formalize the algorithm and its correctness proof.

### Why This Matters

Bridges existence (Lagrange) with computation (algorithm). Connects number theory to computational complexity via quaternion arithmetic and modular square roots.

## Known Results

### What's Already Proven

- `lagrange-four-squares`: Existence theorem (axiomatized, 8 axioms)
- Mathlib has quaternion algebra and modular arithmetic

### Our Goal

Formalize Rabin-Shallit as a computable function with correctness proof in Lean 4.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| lagrange-four-squares | Direct parent, axiomatized | Quaternions, sum of squares |
| gcd-algorithm | Algorithmic number theory | Euclidean algorithm |

## Suggested First Steps

1. Review Rabin-Shallit paper for key algorithmic steps
2. Check Mathlib for `ZMod.sqrt` or modular square root infrastructure
3. Start with the deterministic reduction to sum-of-two-squares subproblem

## Metadata

```yaml
tags: [number-theory, algorithms, quaternions, sum-of-squares]
related_proofs: [lagrange-four-squares, gcd-algorithm]
difficulty: medium
source: gallery-gap
created: 2026-03-30
```

**Significance**: 7/10
**Tractability**: 5/10
