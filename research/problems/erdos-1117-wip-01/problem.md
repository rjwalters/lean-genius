# Problem: Complete Erdős Problem #1117: Maximum Modulus Points on Circles (Work in Progress)

**Slug**: erdos-1117-wip-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap <!-- derived from gallery proof erdos-1117 -->

## Problem Statement

### Formal Statement

$$
f \text{ entire, non-monomial},\ \nu(r)=\#\{|z|=r: |f(z)|=\max_{|w|=r}|f(w)|\};\ \liminf_{r\to\infty}\nu(r)=\infty?
$$

### Plain Language

For a non-monomial entire f, let ν(r) count maximum modulus points on |z|=r. Can lim sup ν(r) = ∞? YES (Herzog–Piranian 1968). Can lim inf ν(r) = ∞? OPEN. Approximate answer by Glücksam–Pardo-Simón (2024).

### Why This Matters

Maximum-modulus point counts probe the geometry of value distribution for entire functions.

## Known Results

### What's Already Proven

- Partial formalization exists in the gallery proof `erdos-1117` (Erdős Problem #1117: Maximum Modulus Points on Circles).

### What's Still Open

- The full statement above remains open / incompletely formalized.

### Our Goal

Formalize $\nu(r)$ and the $\liminf$ question; record Herzog–Piranian's $\limsup=\infty$ result.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1117 | Base formalization this problem completes/extends | see gallery entry |

## Initial Thoughts

### Potential Approaches

1. **Build on the gallery base**: start from `erdos-1117` and discharge its remaining sorries or extend its statement.
   - Why it might work: the scaffolding and definitions already exist.
   - Risk: remaining gaps may encode the genuinely hard core.

### Key Difficulties

- The result is a recognized open (or subtle) problem; a full proof may be out of reach, so target a clean formal statement plus provable partial results.

### What Would a Proof Need?

- A precise Lean formalization of the objects in the statement.
- Supporting lemmas connecting to existing Mathlib theory.

## Tractability Assessment

**Difficulty**: High

**Significance**: 6/10

**Tractability**: 5/10

**Justification**:
- Derived from an established Erdős-problem gallery entry with partial formalization.
- Scope can be narrowed to statement + partial results if the full problem is open.

**Estimated Effort**:
- Exploration: days
- If tractable: weeks
- If hard: unknown

## References

### Papers
- Erdős problem entry (see gallery proof `erdos-1117`).

### Mathlib
- Relevant Mathlib modules for the domain (complex-analysis, entire-functions).

## Metadata

```yaml
tags:
  - erdos
  - complex-analysis
  - entire-functions
  - maximum-modulus
  - value-distribution
  - open
  - wip
related_proofs:
  - erdos-1117
difficulty: high
source: gallery-gap
created: 2026-07-09
```
