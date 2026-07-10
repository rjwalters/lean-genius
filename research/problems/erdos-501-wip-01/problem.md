# Problem: Complete Erdős #501: Independent Sets for Outer Measure Families (Work in Progress)

**Slug**: erdos-501-wip-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap <!-- derived from gallery proof erdos-501 -->

## Problem Statement

### Formal Statement

$$
\{A_x\}_{x} \text{ bounded},\ \lambda^*(A_x)<1 \implies \exists \text{ infinite } I \text{ independent (}x\notin A_y\ \forall x,y\in I)\,?
$$

### Plain Language

For bounded sets A_x with outer measure < 1, must infinite independent sets exist? Answer depends on set-theoretic axioms!

### Why This Matters

Whether infinite independent sets exist is independent of ZFC — a striking set-theoretic dichotomy.

## Known Results

### What's Already Proven

- Partial formalization exists in the gallery proof `erdos-501` (Erdős #501: Independent Sets for Outer Measure Families).

### What's Still Open

- The full statement above remains open / incompletely formalized.

### Our Goal

Formalize outer-measure families and independence; capture the axiom-dependence of the answer.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-501 | Base formalization this problem completes/extends | see gallery entry |

## Initial Thoughts

### Potential Approaches

1. **Build on the gallery base**: start from `erdos-501` and discharge its remaining sorries or extend its statement.
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
- Erdős problem entry (see gallery proof `erdos-501`).

### Mathlib
- Relevant Mathlib modules for the domain (set-theory, measure-theory).

## Metadata

```yaml
tags:
  - erdos
  - set-theory
  - measure-theory
  - combinatorics
  - independence
  - wip
related_proofs:
  - erdos-501
difficulty: high
source: gallery-gap
created: 2026-07-09
```
