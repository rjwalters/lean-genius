# Problem: Complete Erdős Problem #506: Minimum Number of Circles from n Points (Work in Progress)

**Slug**: erdos-506-wip-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap <!-- derived from gallery proof erdos-506 -->

## Problem Statement

### Formal Statement

$$
g(n) = \min \#\{\text{distinct circles through } P\}\ \text{over } n\text{-point } P \text{ not all concyclic};\ g(n) \ge \binom{n-1}{2}\,?
$$

### Plain Language

What is the minimum number of distinct circles determined by n points in ℝ², not all concyclic? Elliott (1967): ≥ C(n-1,2) for n > 393. Segre: fails for n = 8. Open for small n.

### Why This Matters

Circle analogue of the Sylvester–Gallai / ordinary-line problems in combinatorial geometry.

## Known Results

### What's Already Proven

- Partial formalization exists in the gallery proof `erdos-506` (Erdős Problem #506: Minimum Number of Circles from n Points).

### What's Still Open

- The full statement above remains open / incompletely formalized.

### Our Goal

Formalize distinct-circle counts and Elliott's $\binom{n-1}{2}$ bound for $n>393$; note Segre's $n=8$ exception.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-506 | Base formalization this problem completes/extends | see gallery entry |

## Initial Thoughts

### Potential Approaches

1. **Build on the gallery base**: start from `erdos-506` and discharge its remaining sorries or extend its statement.
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
- Erdős problem entry (see gallery proof `erdos-506`).

### Mathlib
- Relevant Mathlib modules for the domain (geometry, combinatorial geometry).

## Metadata

```yaml
tags:
  - erdos
  - geometry
  - combinatorial geometry
  - circles
  - incidence geometry
  - wip
related_proofs:
  - erdos-506
difficulty: high
source: gallery-gap
created: 2026-07-09
```
