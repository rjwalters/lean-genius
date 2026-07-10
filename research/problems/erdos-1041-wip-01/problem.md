# Problem: Complete Erdős Problem #1041: Paths in Polynomial Level Sets (Work in Progress)

**Slug**: erdos-1041-wip-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap <!-- derived from gallery proof erdos-1041 -->

## Problem Statement

### Formal Statement

$$
f \text{ monic},\ \text{roots} \subseteq \overline{\mathbb{D}} \implies \exists \text{ path of length} < 2 \text{ in } \{z:|f(z)|<1\} \text{ joining two roots}
$$

### Plain Language

For a monic polynomial with all roots in the unit disk, must there exist a path of length less than 2 in the sublevel set {z : |f(z)| < 1} connecting two roots?

### Why This Matters

Connectivity of polynomial sublevel sets links complex analysis to metric geometry of lemniscates.

## Known Results

### What's Already Proven

- Partial formalization exists in the gallery proof `erdos-1041` (Erdős Problem #1041: Paths in Polynomial Level Sets).

### What's Still Open

- The full statement above remains open / incompletely formalized.

### Our Goal

Formalize the sublevel set $\{|f|<1\}$ and the path-length-$<2$ connectivity claim between roots.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1041 | Base formalization this problem completes/extends | see gallery entry |

## Initial Thoughts

### Potential Approaches

1. **Build on the gallery base**: start from `erdos-1041` and discharge its remaining sorries or extend its statement.
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
- Erdős problem entry (see gallery proof `erdos-1041`).

### Mathlib
- Relevant Mathlib modules for the domain (complex-analysis, polynomials).

## Metadata

```yaml
tags:
  - erdos
  - complex-analysis
  - polynomials
  - metric-geometry
  - level-sets
  - paths
  - wip
related_proofs:
  - erdos-1041
difficulty: high
source: gallery-gap
created: 2026-07-09
```
