# Problem: Complete Erdős Problem #1168: Negative Partition Relation for ℵ_{ω+1} (Work in Progress)

**Slug**: erdos-1168-wip-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap <!-- derived from gallery proof erdos-1168 -->

## Problem Statement

### Formal Statement

$$
\aleph_{\omega+1} \not\to (\aleph_{\omega+1}, 3, \ldots, 3)^2_{\aleph_0}\ \text{(without assuming GCH)}
$$

### Plain Language

Prove ℵ_{ω+1} ↛ (ℵ_{ω+1}, 3, …, 3)_{ℵ₀}² without GCH. Open problem in set-theoretic combinatorics at the intersection of partition calculus and pcf theory.

### Why This Matters

A partition-calculus / pcf-theory problem at a singular cardinal successor, a frontier of set theory.

## Known Results

### What's Already Proven

- Partial formalization exists in the gallery proof `erdos-1168` (Erdős Problem #1168: Negative Partition Relation for ℵ_{ω+1}).

### What's Still Open

- The full statement above remains open / incompletely formalized.

### Our Goal

Formalize the negative square-bracket partition relation and isolate what a ZFC (no-GCH) proof requires.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1168 | Base formalization this problem completes/extends | see gallery entry |

## Initial Thoughts

### Potential Approaches

1. **Build on the gallery base**: start from `erdos-1168` and discharge its remaining sorries or extend its statement.
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
- Erdős problem entry (see gallery proof `erdos-1168`).

### Mathlib
- Relevant Mathlib modules for the domain (set-theory, ramsey-theory).

## Metadata

```yaml
tags:
  - erdos
  - set-theory
  - ramsey-theory
  - partition-relations
  - cardinals
  - open-conjecture
  - wip
related_proofs:
  - erdos-1168
difficulty: high
source: gallery-gap
created: 2026-07-09
```
