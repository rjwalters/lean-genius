# Problem: Complete Erdős Problem #101: Four-Point Lines from Planar Point Sets (Work in Progress)

**Slug**: erdos-101-wip-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap <!-- derived from gallery proof erdos-101 -->

## Problem Statement

### Formal Statement

$$
n \text{ points in } \mathbb{R}^2,\ \text{no 5 collinear} \implies \#\{\text{lines with exactly 4 points}\} = o(n^2)
$$

### Plain Language

Given n points in ℝ² with no five collinear, is the number of lines containing exactly four points o(n²)? Grünbaum: ≫ n^{3/2}. Solymosi–Stojaković: n^{2−O(1/√log n)}. Open.

### Why This Matters

A central incidence-geometry question; bounds on $k$-rich lines drive extremal combinatorics.

## Known Results

### What's Already Proven

- Partial formalization exists in the gallery proof `erdos-101` (Erdős Problem #101: Four-Point Lines from Planar Point Sets).

### What's Still Open

- The full statement above remains open / incompletely formalized.

### Our Goal

Formalize the incidence setup and the $o(n^2)$ target; capture the Grünbaum lower bound $\gg n^{3/2}$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-101 | Base formalization this problem completes/extends | see gallery entry |

## Initial Thoughts

### Potential Approaches

1. **Build on the gallery base**: start from `erdos-101` and discharge its remaining sorries or extend its statement.
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
- Erdős problem entry (see gallery proof `erdos-101`).

### Mathlib
- Relevant Mathlib modules for the domain (combinatorial-geometry, incidence-geometry).

## Metadata

```yaml
tags:
  - erdos
  - combinatorial-geometry
  - incidence-geometry
  - collinearity
  - open
  - wip
related_proofs:
  - erdos-101
difficulty: high
source: gallery-gap
created: 2026-07-09
```
