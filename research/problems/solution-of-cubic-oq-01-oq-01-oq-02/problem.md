# Problem: Derive the discriminant as the resultant Res(f, f') of the cubic and its deri...

**Slug**: solution-of-cubic-oq-01-oq-01-oq-02
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\Delta(f) \;=\; (-1)^{n(n-1)/2}\,\frac{1}{a_n}\,\mathrm{Res}(f, f') \qquad\text{for } f=\sum a_i X^i,\ \deg f = n
$$

### Plain Language

Show that the discriminant of a cubic (and, more generally, of a polynomial of arbitrary degree) equals the resultant Res(f, f') of the polynomial and its derivative, up to the standard sign/leading-coefficient normalization. Verify that for the cubic this reproduces the coefficient formula already derived in the parent proof.

### Why This Matters

The resultant gives a coordinate-free, degree-uniform definition of the discriminant that does not require knowing the roots. It connects the elementary 'three equal/distinct roots' criterion for cubics to the general theory of resultants and is the cleanest route to discriminants in higher degree.

## Known Results

### What's Already Proven

- Parent `solution-of-cubic-oq-01-oq-01` derives the cubic discriminant explicitly from Cardano's formula and the Tschirnhaus depression.
- Mathlib has `Polynomial.discriminant` and resultant machinery (`Polynomial.resultant`) plus `Polynomial.derivative`.

### What's Still Open

This specific leaf — extracted as an open question from the parent proof `solution-of-cubic-oq-01-oq-01` — has not yet been formalized in the gallery.

### Our Goal

Prove `discriminant f = (sign) * Res(f, f') / leadingCoeff f` for the cubic, matching the parent's coefficient formula, and state the general-degree version.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `solution-of-cubic-oq-01-oq-01` | parent: cubic discriminant from Cardano | Tschirnhaus, Vieta |
| `solution-of-cubic` | Cardano's formula and root structure | field arithmetic |

## Initial Thoughts

### Potential Approaches

1. **Reuse parent machinery**: The parent `solution-of-cubic-oq-01-oq-01` is verified (0-axiom); specialize / instantiate its main results to this leaf rather than re-deriving from scratch.
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
- `Mathlib.RingTheory.Polynomial.Resultant` — resultant of two polynomials.
- `Mathlib.RingTheory.Discriminant` / `Polynomial.discriminant`.
- `Polynomial.derivative`, `Polynomial.roots`.

## Metadata

```yaml
tags:
  - algebra
  - polynomials
  - discriminant
  - resultant
  - research
related_proofs:
  - solution-of-cubic-oq-01-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
