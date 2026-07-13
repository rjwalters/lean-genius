# Problem: Minimal Polynomial Generalization to K-Algebras

**Slug**: cayley-hamilton-minpoly-oq-02-oq-01
**Created**: 2026-03-06
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For elements a, b in a K-algebra A, if a and b are conjugate (isomorphic via an algebra automorphism), then they have the same minimal polynomial over K.

### Plain Language

Can the minimal polynomial theory be generalized from matrices to abstract K-algebras? If two elements of an algebra are related by an isomorphism, they should have the same minimal polynomial.

### Why This Matters

This is a natural generalization of Cayley-Hamilton theory from matrices to abstract algebra, connecting linear algebra with ring theory.

## Known Results

### What's Already Proven

- `CayleyHamiltonMinpolyOQ02.lean` - Minimal polynomial theory for matrices
- Mathlib `minpoly` for general algebra elements
- Cayley-Hamilton theorem for matrices

### Our Goal

Show that algebra isomorphisms preserve minimal polynomials in K-algebras.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cayley-hamilton | Base theorem | Matrix polynomial evaluation |
| cayley-hamilton-minpoly | Minimal polynomial theory | Polynomial division, annihilators |
| cayley-hamilton-minpoly-oq-02 | Isomorphic matrices | Similarity, conjugation |

## Tractability Assessment

**Difficulty**: Medium-High

## Metadata

```yaml
tags:
  - linear-algebra
  - abstract-algebra
  - minimal-polynomial
  - k-algebras
related_proofs:
  - cayley-hamilton
  - cayley-hamilton-minpoly
  - cayley-hamilton-minpoly-oq-02
difficulty: medium-high
source: gallery-gap
created: 2026-03-06
```

**Significance**: 6/10
**Tractability**: 5/10
