# Problem: Irrationality Measures of e, pi, and ln(2)

**Slug**: liouville-theorem-oq-02
**Created**: 2026-03-30
**Status**: Active
**Source**: gallery-gap (open question from liouville-theorem proof)

## Problem Statement

### Formal Statement

The irrationality measure $\mu(\alpha)$ is the infimum of $\mu$ such that $|\alpha - p/q| > q^{-\mu}$ has finitely many rational exceptions. Known: $\mu(e) = 2$, $\mu(\pi) \leq 7.103$, $\mu(\ln 2) \leq 3.574$.

### Plain Language

How well can specific constants be approximated by rationals? The irrationality measure quantifies this. $\mu(e) = 2$ means $e$ is as hard to approximate as a "generic" irrational. Formalize at least $\mu(e) = 2$.

### Why This Matters

Connects Diophantine approximation, continued fractions, and transcendence theory. Extends the gallery's Liouville theorem from algebraic numbers to specific transcendental constants.

## Known Results

### What's Already Proven

- `liouville-theorem`: Approximation bound for algebraic numbers (axiomatized, 2 axioms)
- `e-transcendental`: Transcendence of e

### Our Goal

Formalize $\mu(e) = 2$ using the continued fraction expansion of $e$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| liouville-theorem | Direct parent, axiomatized | Diophantine approximation |
| e-transcendental | Transcendence of e | Hermite-Lindemann |

## Suggested First Steps

1. Check Mathlib for continued fraction API
2. Use $e = [2; 1, 2, 1, 1, 4, 1, 1, 6, ...]$ to bound rational approximations
3. Prove $\mu(e) \leq 2$ from convergent bounds, then $\mu(e) \geq 2$ from Dirichlet

## Metadata

```yaml
tags: [number-theory, transcendental, approximation, diophantine]
related_proofs: [liouville-theorem, e-transcendental]
difficulty: medium
source: gallery-gap
created: 2026-03-30
```

**Significance**: 7/10
**Tractability**: 5/10
