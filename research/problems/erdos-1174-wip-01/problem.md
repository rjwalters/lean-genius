# Problem: Complete Erdős Problem #1174: Monochromatic Cliques from Edge Colorings (Work in Progress)

**Slug**: erdos-1174-wip-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap <!-- derived from gallery proof erdos-1174 -->

## Problem Statement

### Formal Statement

$$
\exists\, K_4\text{-free } G \text{ s.t. every countable edge-colouring of } G \text{ yields a monochromatic triangle}
$$

### Plain Language

Does there exist a K₄-free graph such that every countable edge coloring contains a monochromatic triangle, and does the analogous infinite generalization hold?

### Why This Matters

Bridges finite Ramsey theory with infinite colourings; a partition property strictly below $K_4$.

## Known Results

### What's Already Proven

- Partial formalization exists in the gallery proof `erdos-1174` (Erdős Problem #1174: Monochromatic Cliques from Edge Colorings).

### What's Still Open

- The full statement above remains open / incompletely formalized.

### Our Goal

Formalize the $K_4$-free monochromatic-triangle demand and its infinite generalization.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1174 | Base formalization this problem completes/extends | see gallery entry |

## Initial Thoughts

### Potential Approaches

1. **Build on the gallery base**: start from `erdos-1174` and discharge its remaining sorries or extend its statement.
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
- Erdős problem entry (see gallery proof `erdos-1174`).

### Mathlib
- Relevant Mathlib modules for the domain (combinatorics, graph-theory).

## Metadata

```yaml
tags:
  - erdos
  - combinatorics
  - graph-theory
  - set-theory
  - ramsey-theory
  - open
  - wip
related_proofs:
  - erdos-1174
difficulty: high
source: gallery-gap
created: 2026-07-09
```
