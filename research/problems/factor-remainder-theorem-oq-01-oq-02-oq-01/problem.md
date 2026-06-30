# Problem: Relate this to separability: a polynomial over a field is separable iff it sh...

**Slug**: factor-remainder-theorem-oq-01-oq-02-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
f \text{ separable} \iff \gcd\!\left(f, f^{[1]}\right)=1, \qquad f \text{ irreducible inseparable} \iff f \in K[X^p]\iff \forall\, 1\le k\le p-1,\ f^{[k]} = 0
$$

### Plain Language

Relate the parent's Hasse-derivative root-multiplicity criterion to separability: a polynomial over a field is separable iff it shares no root with its first Hasse derivative, and an irreducible polynomial is inseparable iff it is a polynomial in X^p, equivalently all its Hasse derivatives up to order p-1 vanish.

### Why This Matters

Separability is the dividing line in field theory between the well-behaved (characteristic 0, finite fields) and the subtle (inseparable extensions in characteristic p). Tying it to the already-formalized Hasse-derivative multiplicity test gives a computational handle on separability and inseparability.

## Known Results

### What's Already Proven

- Parent `factor-remainder-theorem-oq-01-oq-02` formalizes root multiplicity via Hasse derivatives (`Polynomial.hasseDeriv`).
- Mathlib has `Polynomial.Separable`, `Polynomial.separable_iff_squarefree`, `Polynomial.Separable.squarefree`, and characteristic-p tooling (`expand`, `Polynomial.expand_contract`).

### What's Still Open

This specific leaf — extracted as an open question from the parent proof `factor-remainder-theorem-oq-01-oq-02` — has not yet been formalized in the gallery.

### Our Goal

Prove the separable ⟺ gcd(f, f') = 1 characterization using the parent's Hasse-derivative results, and characterize inseparable irreducibles as elements of K[X^p] via vanishing Hasse derivatives.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `factor-remainder-theorem-oq-01-oq-02` | parent: Hasse-derivative multiplicity test | Hasse derivative, Taylor |
| `factor-remainder-theorem` | factor/remainder theorem, root multiplicity | polynomial division |

## Initial Thoughts

### Potential Approaches

1. **Reuse parent machinery**: The parent `factor-remainder-theorem-oq-01-oq-02` is verified (0-axiom); specialize / instantiate its main results to this leaf rather than re-deriving from scratch.
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
- `Mathlib.FieldTheory.Separable` — `Polynomial.Separable`, separable ⟺ squarefree.
- `Polynomial.hasseDeriv`, `Polynomial.expand`.
- `Mathlib.RingTheory.Polynomial.Content` for gcd/primitive parts.

## Metadata

```yaml
tags:
  - algebra
  - polynomials
  - separability
  - hasse-derivative
  - positive-characteristic
  - research
related_proofs:
  - factor-remainder-theorem-oq-01-oq-02
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
