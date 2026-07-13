# Problem: Extract the Faddeev–LeVerrier recurrence for the coefficients of invPoly from...

**Slug**: cayley-hamilton-minpoly-oq-07-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
c_0 = 1,\quad M_k = A\,M_{k-1} + c_{k-1} I,\quad c_k = -\tfrac{1}{k}\,\mathrm{tr}(A M_{k-1}); \quad A^{-1} = -\tfrac{1}{c_n} M_{n-1}
$$

### Plain Language

Extract the Faddeev–LeVerrier recurrence for the coefficients of the inverse/characteristic polynomial from the Newton identities, giving an explicit, division-light algorithm that simultaneously computes the characteristic polynomial coefficients and (when invertible) the matrix inverse.

### Why This Matters

Faddeev–LeVerrier is the classical closed-form algorithm linking traces of powers of A to the characteristic-polynomial coefficients and to A^{-1}. Formalizing its recurrence turns the parent's invPoly construction into an explicit, verifiable algorithm and connects Cayley–Hamilton to Newton's identities.

## Known Results

### What's Already Proven

- Parent `cayley-hamilton-minpoly-oq-07` constructs invPoly / the adjugate-based inverse polynomial.
- Mathlib: `Matrix.charpoly`, `Matrix.trace`, `Matrix.adjugate`, Cayley–Hamilton (`Matrix.aeval_self_charpoly`), Newton's identities.

### What's Still Open

This specific leaf — extracted as an open question from the parent proof `cayley-hamilton-minpoly-oq-07` — has not yet been formalized in the gallery.

### Our Goal

Define the Faddeev–LeVerrier recurrence (M_k, c_k) and prove it computes the characteristic-polynomial coefficients and the inverse, derived from the Newton identities.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `cayley-hamilton-minpoly-oq-07` | parent: invPoly / inverse polynomial | adjugate, charpoly |
| `cayley-hamilton-minpoly` | Cayley–Hamilton and minimal polynomial | linear algebra |

## Initial Thoughts

### Potential Approaches

1. **Reuse parent machinery**: The parent `cayley-hamilton-minpoly-oq-07` is verified (0-axiom); specialize / instantiate its main results to this leaf rather than re-deriving from scratch.
2. **Lean directly on Mathlib**: Several of the required notions already exist in Mathlib (see References); the work is connecting them to the parent's statement.

### What Would a Proof Need?

- Import and apply the parent proof's verified lemmas.
- Bridge lemmas connecting the parent's formulation to standard Mathlib definitions.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Direct extension of a verified, 0-axiom parent proof.
- Required supporting definitions exist in Mathlib.
- Clear first step: instantiate / specialize the parent result.

## References

### Mathlib
- `Mathlib.LinearAlgebra.Matrix.Charpoly.*` — charpoly, Cayley–Hamilton.
- `Matrix.trace`, `Matrix.adjugate`, Newton-identity lemmas.

## Metadata

```yaml
tags:
  - linear-algebra
  - cayley-hamilton
  - characteristic-polynomial
  - matrix-inverse
  - research
related_proofs:
  - cayley-hamilton-minpoly-oq-07
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
