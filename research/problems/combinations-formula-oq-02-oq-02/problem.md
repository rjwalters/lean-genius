# Problem: Direct closed form C_n = C(2n,n)/(n+1) for Catalan numbers

**Slug**: combinations-formula-oq-02-oq-02
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
C_n \;=\; \frac{1}{n+1}\binom{2n}{n},\qquad\text{equivalently}\qquad (n+1)\,C_n = \binom{2n}{n}.
$$

### Plain Language

Prove the central-binomial closed form for the Catalan numbers **directly**, without
routing through the identity `catalan_mul_succ` used in the parent entry
`combinations-formula-oq-02`. Give a self-contained derivation of
`C_n = C(2n,n)/(n+1)`.

### Why This Matters

The closed form is the canonical formula for the Catalan numbers; a direct proof
independent of the recurrence-based `catalan_mul_succ` route provides an alternative,
more elementary derivation and a reusable central-binomial lemma.

## Known Results

### What's Already Proven

- Parent `combinations-formula-oq-02`: Catalan closed form via `catalan_mul_succ`.
- Mathlib: `Nat.catalan`, `Nat.catalan_eq_centralBinom_div`, `Nat.centralBinom`,
  `Nat.succ_mul_catalan_eq_centralBinom`.

### Our Goal

Establish `(n+1) * catalan n = centralBinom n` (and the divided form) by a direct
argument — e.g. via the reflection/ballot count or `centralBinom` divisibility — rather
than the parent's `catalan_mul_succ` chain.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| combinations-formula-oq-02 | parent; same closed form, different route | catalan recurrence |

## Initial Thoughts

### Potential Approaches

1. **Mathlib bridge**: use `Nat.succ_mul_catalan_eq_centralBinom` /
   `Nat.catalan_eq_centralBinom_div` directly.
   - Risk: must ensure the "direct" requirement is met (not the parent's lemma).
2. **Combinatorial**: ballot-sequence / cycle-lemma count giving `C(2n,n) − C(2n,n+1)`.
   - Risk: more formalization effort for the bijection.

## Tractability Assessment

**Difficulty**: Medium

**Justification**: Mathlib already contains `centralBinom` Catalan bridges; the work is
selecting a route distinct from the parent and assembling a clean statement.

## References

### Mathlib
- `Mathlib.Combinatorics.Catalan` — `Nat.catalan`, `centralBinom`, division lemmas.

## Metadata

```yaml
tags:
  - combinatorics
  - catalan-numbers
  - binomial-coefficients
  - central-binomial
related_proofs:
  - combinations-formula-oq-02
difficulty: medium
source: gallery-gap
created: 2026-07-01
```

**Significance**: 5/10
**Tractability**: 7/10
