# Problem: Complete Erdős Problem #1173: Free Sets for Set Mappings under GCH (Work in Progress)

**Slug**: erdos-1173-wip-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap <!-- derived from gallery proof erdos-1173 -->

## Problem Statement

### Formal Statement

$$
\text{set mapping } F \text{ of order} <\aleph_{\omega+1} \text{ on } \aleph_{\omega+1} \implies \exists \text{ free set of size } \aleph_{\omega+1}\ (\text{under GCH})
$$

### Plain Language

Does there exist a free set of cardinality ℵ_{ω+1}?

### Why This Matters

Free-set theorems for set mappings underpin combinatorial set theory of singular cardinals.

## Known Results

### What's Already Proven

- Partial formalization exists in the gallery proof `erdos-1173` (Erdős Problem #1173: Free Sets for Set Mappings under GCH).

### What's Still Open

- The full statement above remains open / incompletely formalized.

### Our Goal

Formalize set mappings and free sets; state the GCH free-set existence claim at $\aleph_{\omega+1}$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1173 | Base formalization this problem completes/extends | see gallery entry |

## Initial Thoughts

### Potential Approaches

1. **Build on the gallery base**: start from `erdos-1173` and discharge its remaining sorries or extend its statement.
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
- Erdős problem entry (see gallery proof `erdos-1173`).

### Mathlib
- Relevant Mathlib modules for the domain (combinatorics, set-theory).

## Metadata

```yaml
tags:
  - erdos
  - combinatorics
  - set-theory
  - open
  - wip
related_proofs:
  - erdos-1173
difficulty: high
source: gallery-gap
created: 2026-07-09
```
