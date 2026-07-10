# Problem: Complete Erdős Problem #1092: Chromatic Decomposition Threshold (Work in Progress)

**Slug**: erdos-1092-wip-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap <!-- derived from gallery proof erdos-1092 -->

## Problem Statement

### Formal Statement

$$
f_2(n) = \max\{m: \text{removing} \le m \text{ edges from every subgraph keeps } \chi \le 2,\ \text{yet } \chi(G)\le 3\};\ f_2(n) \gg n?
$$

### Plain Language

Let f_r(n) be max edges removable from each subgraph to reduce chromatic number to ≤ r while forcing χ(G) ≤ r+1. Is f₂(n) ≫ n? Rödl (1982) gives f₂(n) = O(n·polylog). Open.

### Why This Matters

Quantifies how far a graph can be from bipartite while remaining locally 2-degenerate in chromatic terms.

## Known Results

### What's Already Proven

- Partial formalization exists in the gallery proof `erdos-1092` (Erdős Problem #1092: Chromatic Decomposition Threshold).

### What's Still Open

- The full statement above remains open / incompletely formalized.

### Our Goal

Formalize $f_r(n)$ and the $f_2(n)\gg n$ question; record Rödl's $O(n\,\mathrm{polylog})$ upper bound.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1092 | Base formalization this problem completes/extends | see gallery entry |

## Initial Thoughts

### Potential Approaches

1. **Build on the gallery base**: start from `erdos-1092` and discharge its remaining sorries or extend its statement.
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
- Erdős problem entry (see gallery proof `erdos-1092`).

### Mathlib
- Relevant Mathlib modules for the domain (graph-theory, chromatic-number).

## Metadata

```yaml
tags:
  - erdos
  - graph-theory
  - chromatic-number
  - extremal-graph-theory
  - open
  - wip
related_proofs:
  - erdos-1092
difficulty: high
source: gallery-gap
created: 2026-07-09
```
