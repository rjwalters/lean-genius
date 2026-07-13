# Problem: Primitive Roots Modulo Primes

**Slug**: primitive-roots-count
**Created**: 2025-12-31
**Status**: Graduated (Completed)
**Tier**: B

## Problem Statement

### Formal Statement

$$
\text{For prime } p, \text{ there are exactly } \phi(p-1) \text{ primitive roots mod } p
$$

### Plain Language

For any prime p, the multiplicative group (ℤ/pℤ)* is cyclic, and the number of generators (primitive roots) equals Euler's totient of p-1.

### Why This Matters

1. **Fundamental group theory** — Cyclic structure of units mod p
2. **Cryptographic applications** — Primitive roots used in DH key exchange
3. **Elegant Mathlib proof** — Uses isCyclic_of_subgroup_isDomain

## Known Results

### What's Already Proven

- **Existence** — (ℤ/pℤ)* is cyclic for prime p
- **Count** — Exactly φ(p-1) primitive roots
- **Generator characterization** — a is primitive root ↔ ord(a) = p-1
- **Examples** — p = 2, 3, 5, 7, 11, 13 with explicit primitive roots

### Our Goal

✅ Complete — Full proof using Mathlib's group theory.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| None yet | - | - |

## Tractability Assessment

**Significance**: 6/10
**Tractability**: 6/10

## References

### Mathlib
- `Mathlib.GroupTheory.SpecificGroups.Cyclic` — Cyclic groups
- `IsCyclic.card_orderOf_eq_totient` — Primitive root count

## Metadata

```yaml
tags:
  - number-theory
  - group-theory
  - classical
  - primitive-roots
significance: 6
tractability: 6
tier: B
```
