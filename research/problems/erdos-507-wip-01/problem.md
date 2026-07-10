# Problem: Complete Erdős Problem #507: Heilbronn's Triangle Problem (Work in Progress)

**Slug**: erdos-507-wip-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap <!-- derived from gallery proof erdos-507 -->

## Problem Statement

### Formal Statement

$$
\alpha(n) = \min_{|P|=n,\,P\subseteq \mathbb{D}}\ \max_{\triangle \subseteq P} \text{area};\ \frac{\log n}{n^2} \ll \alpha(n) \ll n^{-7/6+o(1)}
$$

### Plain Language

Estimate α(n), the smallest area such that every n-point set in the unit disk contains a triangle of area ≤ α(n). Best bounds: (log n)/n² ≪ α(n) ≪ 1/n^{7/6+o(1)}. Status: OPEN.

### Why This Matters

Heilbronn's triangle problem is a canonical extremal geometry question with a large bound gap.

## Known Results

### What's Already Proven

- Partial formalization exists in the gallery proof `erdos-507` (Erdős Problem #507: Heilbronn's Triangle Problem).

### What's Still Open

- The full statement above remains open / incompletely formalized.

### Our Goal

Formalize $\alpha(n)$ and record the current best lower/upper bounds.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-507 | Base formalization this problem completes/extends | see gallery entry |

## Initial Thoughts

### Potential Approaches

1. **Build on the gallery base**: start from `erdos-507` and discharge its remaining sorries or extend its statement.
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
- Erdős problem entry (see gallery proof `erdos-507`).

### Mathlib
- Relevant Mathlib modules for the domain (geometry, discrete-geometry).

## Metadata

```yaml
tags:
  - erdos
  - geometry
  - discrete-geometry
  - combinatorial-geometry
  - open
  - wip
related_proofs:
  - erdos-507
difficulty: high
source: gallery-gap
created: 2026-07-09
```
