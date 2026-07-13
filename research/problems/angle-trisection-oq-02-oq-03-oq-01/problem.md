# Problem: Gauss-Wantzel Theorem from Mathlib Cyclotomic Fields

**Slug**: angle-trisection-oq-02-oq-03-oq-01
**Created**: 2026-03-06
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

A regular n-gon is constructible by compass and straightedge if and only if n = 2^k * p_1 * p_2 * ... * p_m where each p_i is a distinct Fermat prime.

### Plain Language

Can the Gauss-Wantzel axiom (currently assumed in the proof) be proved from Mathlib's existing cyclotomic field infrastructure? The ingredients (`IsCyclotomicExtension`, `ZMod.unitsEquivCoprime`, degree computation) exist but need ~300 lines of assembly.

### Why This Matters

This is a classic constructibility result connecting geometry with algebra (Galois theory). Proving it from Mathlib foundations would remove an axiom from our formalization.

## Known Results

### What's Already Proven

- `AngleTrisectionOQ02OQ03.lean` - Gauss-Wantzel formalization with axiom
- Mathlib `IsCyclotomicExtension` infrastructure
- `ZMod.unitsEquivCoprime` for Euler totient connections

### What's Still Open

- Assembly of Mathlib cyclotomic + Galois tools into the constructibility proof
- Connecting degree of cyclotomic extension to power-of-2 criterion

### Our Goal

Prove the Gauss-Wantzel axiom as a theorem using Mathlib's cyclotomic field theory.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| angle-trisection | Base impossibility proof | Field extensions, degree arguments |
| angle-trisection-oq-02 | Constructible algebraic numbers | Galois groups, 2-groups |
| angle-trisection-oq-02-oq-03 | Gauss-Wantzel statement | Cyclotomic extensions, Fermat primes |

## Initial Thoughts

### Potential Approaches

1. **Direct cyclotomic assembly**: Use `IsCyclotomicExtension` to compute the degree of Q(zeta_n)/Q, then show constructibility iff this degree is a power of 2.
   - Why it might work: All pieces exist in Mathlib
   - Risk: Connecting different API layers may be intricate

### Key Difficulties

- Bridging between Galois theory API and constructibility definitions
- Computing the degree of cyclotomic extensions for composite n

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathlib has the algebraic infrastructure
- The proof sketch suggests ~300 lines of assembly
- Similar "API assembly" proofs have succeeded before

## Metadata

```yaml
tags:
  - geometry
  - galois-theory
  - field-theory
  - constructibility
  - fermat-primes
related_proofs:
  - angle-trisection
  - angle-trisection-oq-02
  - angle-trisection-oq-02-oq-03
difficulty: medium
source: gallery-gap
created: 2026-03-06
```

**Significance**: 7/10
**Tractability**: 6/10
