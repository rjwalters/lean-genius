# Problem: Complete proof of Erdős Problem #1049: Irrationality of Divisor Sums

**Slug**: erdos-1049-incomplete-01
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap <!-- derived from gallery proof erdos-1049 -->

## Problem Statement

### Formal Statement

$$
t \in \mathbb{Q},\ t>1 \implies \sum_{n\ge 1} \frac{1}{t^n-1} = \sum_{n\ge 1}\frac{\tau(n)}{t^n} \notin \mathbb{Q}
$$

### Plain Language

For rational t > 1, is ∑_{n≥1} 1/(t^n - 1) = ∑_{n≥1} τ(n)/t^n irrational? OPEN: Erdős proved YES for integer t ≥ 2. Chowla's conjecture for all rationals unresolved.

### Why This Matters

Irrationality of Lambert-type divisor series; Erdős settled integer $t$, Chowla's rational case is open.

## Known Results

### What's Already Proven

- Partial formalization exists in the gallery proof `erdos-1049` (Erdős Problem #1049: Irrationality of Divisor Sums).

### What's Still Open

- The full statement above remains open / incompletely formalized.

### Our Goal

Complete the 9 sorries: formalize the series identity and Erdős's irrationality proof for integer $t\ge 2$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1049 | Base formalization this problem completes/extends | see gallery entry |

## Initial Thoughts

### Potential Approaches

1. **Build on the gallery base**: start from `erdos-1049` and discharge its remaining sorries or extend its statement.
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
- Erdős problem entry (see gallery proof `erdos-1049`).

### Mathlib
- Relevant Mathlib modules for the domain (number-theory, irrationality).

## Metadata

```yaml
tags:
  - erdos
  - number-theory
  - irrationality
  - divisor-function
  - series
  - open-problem
  - incomplete
related_proofs:
  - erdos-1049
difficulty: medium
source: gallery-gap
created: 2026-07-09
```
