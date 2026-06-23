# Problem: Euler-Maclaurin Asymptotics for Power Sums

**Slug**: sum-of-kth-powers-oq-04-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\sum_{i=0}^{n-1} i^k / n^{k+1} \to \frac{1}{k+1} \text{ as } n \to \infty
$$

### Plain Language

Show the Riemann sum for x^k on [0,1] converges. The Lean file axiomatizes Bernoulli polynomial leading behavior (1 axiom) and has 1 sorry for the main asymptotics.

### Why This Matters

See `src/data/proofs/sum-of-kth-powers-oq-04/meta.json` for full context. This is a targeted completion/extension of an existing gallery proof.

## Known Results

### What's Already Proven

- Parent proof `sum-of-kth-powers-oq-04` provides the foundation
- sorries to fill: 1 (plus any axioms — check source proof)

### Our Goal

Use squeeze theorem or comparison with integrals. Check if Mathlib's MeasureTheory.integral_pow can be applied via Riemann sum approximation.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `sum-of-kth-powers-oq-04` | Direct parent — inspect its Lean file for sorry locations |

## Tractability Assessment

**Difficulty**: Medium

## Metadata

```yaml
tags:
  - analysis
  - number-theory
  - euler-maclaurin
  - asymptotic
related_proofs:
  - sum-of-kth-powers-oq-04
difficulty: medium
source: gallery-gap
created: 2026-04-03
```

**Significance**: 6/10
**Tractability**: 7/10
