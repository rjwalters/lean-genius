# Problem: Complete Erdős Problem #104: Unit Circles Through Three Points (Work in Progress)

**Slug**: erdos-104-wip-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap <!-- derived from gallery proof erdos-104 -->

## Problem Statement

### Formal Statement

$$
n \text{ points in } \mathbb{R}^2 \implies \#\{\text{unit circles containing} \ge 3 \text{ points}\} = O(n^{3/2})
$$

### Plain Language

Given n points in ℝ², how many unit circles contain at least 3 points? Known: Ω(n^{3/2}) ≤ answer ≤ O(n²). Conjecture: O(n^{3/2}). OPEN ($100 prize).

### Why This Matters

A \$100 Erdős prize problem tightening incidence bounds between $\Omega(n^{3/2})$ and $O(n^2)$.

## Known Results

### What's Already Proven

- Partial formalization exists in the gallery proof `erdos-104` (Erdős Problem #104: Unit Circles Through Three Points).

### What's Still Open

- The full statement above remains open / incompletely formalized.

### Our Goal

Formalize unit-circle incidences and record the known $\Omega(n^{3/2})$ lower and $O(n^2)$ upper bounds.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-104 | Base formalization this problem completes/extends | see gallery entry |

## Initial Thoughts

### Potential Approaches

1. **Build on the gallery base**: start from `erdos-104` and discharge its remaining sorries or extend its statement.
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
- Erdős problem entry (see gallery proof `erdos-104`).

### Mathlib
- Relevant Mathlib modules for the domain (discrete-geometry, incidences).

## Metadata

```yaml
tags:
  - erdos
  - discrete-geometry
  - incidences
  - unit-circles
  - open-problem
  - wip
related_proofs:
  - erdos-104
difficulty: high
source: gallery-gap
created: 2026-07-09
```
