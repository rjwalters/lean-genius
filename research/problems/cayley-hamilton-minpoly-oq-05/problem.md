# Problem: Complete sorry in minpoly_eq_map_of_irreducible

**Slug**: cayley-hamilton-minpoly-oq-05-oq-01
**Created**: 2026-03-22
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

Given a scalar tower $K \to L \to A$ where $A$ is a $K$-algebra, and an element $x \in A$ whose minimal polynomial over $K$ is irreducible, show that the associated monic polynomials (minimal polynomial mapped from $K[X]$ to $L[X]$, vs. the minimal polynomial computed directly over $L$) are equal.

### Plain Language

When you have an irreducible minimal polynomial over a smaller field $K$ and extend scalars to a larger field $L$, the minimal polynomial doesn't change — it's still the same polynomial, just viewed in the larger ring. This is a concrete sorry in the existing formalization that needs filling.

### Why This Matters

This is a key lemma in the theory of minimal polynomials over scalar towers, which underpins the Cayley-Hamilton theorem's generalization to arbitrary $K$-algebras. Completing this sorry would make the existing formalization more robust.

## Known Results

### What's Already Proven

- `Mathlib.FieldTheory.Minpoly.Basic` — core minimal polynomial API
- `Mathlib.FieldTheory.Minpoly.Field` — minimal polynomials over fields
- `Mathlib.RingTheory.Polynomial.ScaleRoots` — polynomial scaling operations
- The surrounding proof architecture is in place in `cayley-hamilton-minpoly`

### What's Still Open

- The specific sorry in `minpoly_eq_map_of_irreducible`

### Our Goal

Fill in the sorry: show that when the minimal polynomial over $K$ is irreducible, mapping it to $L[X]$ gives the minimal polynomial over $L$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cayley-hamilton | Core theorem | Matrix polynomial evaluation |
| cayley-hamilton-minpoly | Direct parent | Minimal polynomial reduction |
| cayley-hamilton-minpoly-oq-05 | Immediate parent | Scalar tower extensions |

## Initial Thoughts

### Potential Approaches

1. **Use irreducibility + minimality**: The mapped polynomial divides minpoly over L, and irreducibility forces equality up to associates. Since both are monic, they must be equal.
   - Why it might work: Standard argument in field theory
   - Risk: Lean's API for polynomial divisibility in scalar towers may be incomplete

2. **Use `Polynomial.map_dvd` + degree bounds**: Show the degree can't decrease when extending scalars for irreducible polynomials.
   - Why it might work: Clean proof via degree arguments
   - Risk: Need degree-preservation lemmas for polynomial maps

### Key Difficulties

- Navigating Lean's `Polynomial.map` and `algebraMap` coercions in scalar towers
- Finding the right Mathlib lemmas for irreducible polynomial behavior under ring maps

### What Would a Proof Need?

- `minpoly.dvd` — the minimal polynomial divides any annihilating polynomial
- `Irreducible.associated_of_dvd` — irreducible elements have trivial divisors
- `Polynomial.Monic.eq_of_associated` — associated monic polynomials are equal

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical argument is well-known and straightforward
- Mathlib has extensive polynomial and minimal polynomial infrastructure
- The sorry is concrete and self-contained

**Estimated Effort**:
- Exploration: 2-4 hours
- If tractable: 1-2 days

## References

### Mathlib
- `Mathlib.FieldTheory.Minpoly.Basic` — minimal polynomial definitions
- `Mathlib.FieldTheory.Minpoly.Field` — field-specific results
- `Mathlib.RingTheory.Polynomial.Basic` — polynomial ring theory

## Metadata

```yaml
tags:
  - linear-algebra
  - abstract-algebra
  - minimal-polynomial
  - field-extensions
  - scalar-tower
related_proofs:
  - cayley-hamilton
  - cayley-hamilton-minpoly
difficulty: medium
source: proof-suggestion
created: 2026-03-22
```

**Significance**: 7/10
**Tractability**: 6/10
