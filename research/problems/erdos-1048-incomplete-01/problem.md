# Problem: Complete proof of Erdős Problem #1048: Polynomial Lemniscate Diameter

**Slug**: erdos-1048-incomplete-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap <!-- derived from gallery proof erdos-1048 -->

## Problem Statement

### Formal Statement

$$
f \text{ monic, roots in } |z|\le r,\ r<2 \implies \{z:|f(z)|<1\} \text{ has a component of diameter} > 2-r\ (\text{FALSE for } r>1)
$$

### Plain Language

For a monic polynomial f ∈ ℂ[x] with roots in |z| ≤ r where r < 2, must L(f,1) = {z : |f(z)| < 1} have a component with diameter > 2-r? DISPROVED by Pommerenke (1961) for r > 1.

### Why This Matters

Pommerenke's disproof calibrates how lemniscate geometry fails naive diameter lower bounds.

## Known Results

### What's Already Proven

- Partial formalization exists in the gallery proof `erdos-1048` (Erdős Problem #1048: Polynomial Lemniscate Diameter).

### What's Still Open

- The full statement above remains open / incompletely formalized.

### Our Goal

Complete the 10 remaining sorries: formalize the lemniscate diameter claim and Pommerenke's counterexample for $r>1$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1048 | Base formalization this problem completes/extends | see gallery entry |

## Initial Thoughts

### Potential Approaches

1. **Build on the gallery base**: start from `erdos-1048` and discharge its remaining sorries or extend its statement.
   - Why it might work: the scaffolding and definitions already exist.
   - Risk: remaining gaps may encode the genuinely hard core.

### Key Difficulties

- The result is a recognized open (or subtle) problem; a full proof may be out of reach, so target a clean formal statement plus provable partial results.

### What Would a Proof Need?

- A precise Lean formalization of the objects in the statement.
- Supporting lemmas connecting to existing Mathlib theory.

## Tractability Assessment

**Difficulty**: Medium

**Significance**: 6/10

**Tractability**: 3/10

**Justification**:
- Derived from an established Erdős-problem gallery entry with partial formalization.
- Scope can be narrowed to statement + partial results if the full problem is open.

**Estimated Effort**:
- Exploration: days
- If tractable: weeks
- If hard: unknown

## References

### Papers
- Erdős problem entry (see gallery proof `erdos-1048`).

### Mathlib
- Relevant Mathlib modules for the domain (analysis, complex-analysis).

## Metadata

```yaml
tags:
  - erdos
  - analysis
  - complex-analysis
  - polynomials
  - lemniscates
  - disproved
  - incomplete
related_proofs:
  - erdos-1048
difficulty: medium
source: gallery-gap
created: 2026-07-09
```
