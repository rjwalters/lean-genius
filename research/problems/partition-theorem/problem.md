# Problem: Rogers-Ramanujan and Schur Partition Identities

**Slug**: partition-theorem-oq-01
**Created**: 2026-03-11
**Status**: Active
**Source**: gallery-extension

## Problem Statement

### Formal Statement

**Rogers-Ramanujan Identity (First):**
The number of partitions of n where parts differ by at least 2 equals the number of partitions into parts congruent to 1 or 4 (mod 5).

**Schur's Theorem (1926):**
The number of partitions of n into parts congruent to +/-1 (mod 6) equals the number of partitions into parts where consecutive parts differ by at least 3.

### Plain Language

Can we formalize the Rogers-Ramanujan identities and Schur's partition theorem in Lean 4, extending the existing Euler partition theorem formalization?

### Why This Matters

The Rogers-Ramanujan identities are among the most beautiful results in combinatorics, connecting partition theory with modular forms, representation theory, and statistical mechanics.

## Known Results

### What's Already Proven

- Euler's partition theorem (distinct = odd) — `proofs/Proofs/PartitionTheorem.lean` (fully proved via Mathlib)
- Mathlib has `Nat.Partition` with parts, sum constraints, and generating function framework
- Computational verification for small cases via `native_decide`

### What's Still Open

- Rogers-Ramanujan identities not in Mathlib
- Schur's partition theorem not in Mathlib

### Our Goal

Formalize at least one of: Rogers-Ramanujan first identity or Schur's theorem, with combinatorial interpretation and computational verification.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| partition-theorem | Direct extension — same partition framework | Generating functions, `Nat.Partition`, `native_decide` |

## Initial Thoughts

### Potential Approaches

1. **Generating function approach**: Extend Euler's framework to Rogers-Ramanujan q-series
2. **Bijective approach (Schur's theorem)**: Direct combinatorial bijection

### Key Difficulties

- Gap conditions ("parts differ by at least k") need careful formalization
- Congruence conditions on parts need arithmetic infrastructure

## Tractability Assessment

**Difficulty**: Challenging

**Justification**:
- Euler's theorem provides a template
- Mathlib has partition infrastructure to build on

## Metadata

```yaml
tags:
  - combinatorics
  - number-theory
  - partition
related_proofs:
  - partition-theorem
difficulty: challenging
source: gallery-extension
created: 2026-03-11
```
