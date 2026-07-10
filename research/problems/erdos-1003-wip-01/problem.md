# Problem: Complete Erdős Problem #1003: Consecutive Equal Totients (Work in Progress)

**Slug**: erdos-1003-wip-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap <!-- derived from gallery proof erdos-1003 -->

## Problem Statement

### Formal Statement

$$
\forall k \ge 1,\ \left|\{n \in \mathbb{N} : \varphi(n)=\varphi(n+1)=\cdots=\varphi(n+k)\}\right| = \infty
$$

### Plain Language

Are there infinitely many solutions to φ(n) = φ(n+1), where φ is the Euler totient function? Erdős conjectured yes, and made the stronger claim that φ(n) = φ(n+1) = ... = φ(n+k) has infinitely many solutions for every k ≥ 1.

### Why This Matters

Euler's totient is central to number theory; equal consecutive values probe its fine multiplicative structure.

## Known Results

### What's Already Proven

- Partial formalization exists in the gallery proof `erdos-1003` (Erdős Problem #1003: Consecutive Equal Totients).

### What's Still Open

- The full statement above remains open / incompletely formalized.

### Our Goal

Formalize the statement and establish the $k=1$ case (infinitely many $n$ with $\varphi(n)=\varphi(n+1)$), or reduce it to a clean sieve criterion.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1003 | Base formalization this problem completes/extends | see gallery entry |

## Initial Thoughts

### Potential Approaches

1. **Build on the gallery base**: start from `erdos-1003` and discharge its remaining sorries or extend its statement.
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
- Erdős problem entry (see gallery proof `erdos-1003`).

### Mathlib
- Relevant Mathlib modules for the domain (number-theory, totient-function).

## Metadata

```yaml
tags:
  - erdos
  - number-theory
  - totient-function
  - consecutive-values
  - asymptotic-density
  - open-problem
  - wip
related_proofs:
  - erdos-1003
difficulty: high
source: gallery-gap
created: 2026-07-09
```
