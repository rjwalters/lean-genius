# Problem: CRT Ring Isomorphism Z/mnZ = Z/mZ x Z/nZ

**Slug**: bezout-identity-oq-03-oq-01
**Created**: 2026-03-06
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For coprime m, n: Z/mnZ is ring-isomorphic to Z/mZ x Z/nZ.

### Plain Language

Can the Chinese Remainder Theorem ring isomorphism be formalized in Lean 4 building on `crt_via_bezout`? This is the algebraic formulation: the map sending x mod mn to (x mod m, x mod n) is a ring isomorphism when gcd(m,n) = 1.

### Why This Matters

CRT is fundamental in number theory and computer science. A clean Lean formalization would demonstrate the algebra-number theory bridge.

## Known Results

### What's Already Proven

- `BezoutIdentityOQ03.lean` - CRT via Bezout coefficients
- Mathlib `ZMod.chineseRemainder` - exists but may not match our formulation
- Bezout identity and GCD algorithms formalized

### What's Still Open

- Ring isomorphism formulation building on our Bezout approach
- Clean connection between Bezout coefficients and the CRT isomorphism

### Our Goal

Formalize the ring isomorphism Z/mnZ = Z/mZ x Z/nZ using our existing Bezout/CRT infrastructure.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| bezout-identity | Base Bezout identity | GCD, extended Euclidean |
| bezout-identity-oq-03 | CRT via Bezout | Number theory, modular arithmetic |

## Tractability Assessment

**Difficulty**: Medium

## Metadata

```yaml
tags:
  - number-theory
  - algebra
  - crt
  - ring-theory
  - bezout
related_proofs:
  - bezout-identity
  - bezout-identity-oq-03
difficulty: medium
source: gallery-gap
created: 2026-03-06
```

**Significance**: 7/10
**Tractability**: 7/10
