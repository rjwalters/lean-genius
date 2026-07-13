# Problem: Self-Duality of Desargues' Theorem

**Slug**: desargues-theorem
**Created**: 2026-03-11
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $\mathcal{P}$ be a projective plane with duality map $\delta$ (swapping points and lines). Then:

$$
\text{Desargues}(\mathcal{P}) \iff \delta(\text{Desargues}(\mathcal{P}))
$$

That is, Desargues' theorem is self-dual: the dual statement (perspective from a line implies perspective from a point) is exactly the converse.

### Plain Language

Desargues' theorem says: if two triangles are in perspective from a point (their corresponding vertices are joined by concurrent lines), then they are in perspective from a line (the intersections of corresponding sides are collinear). The remarkable fact is that swapping "point" and "line" throughout gives the converse. We want to formalize this self-duality explicitly.

### Why This Matters

Self-duality is one of the most beautiful aspects of projective geometry. Formalizing it demonstrates the power of the duality principle and shows how Desargues' theorem occupies a special position in the foundations of geometry (it's equivalent to the coordinatization of projective planes by division rings).

## Known Results

### What's Already Proven

- Desargues' theorem (forward direction) — `desargues-theorem` gallery proof
- Moulton plane counterexample — `desargues-theorem-oq-02` research

### What's Still Open

- Explicit duality transformation in Lean
- Self-duality proof (dual = converse)

### Our Goal

Define a formal duality map on projective plane structures, apply it to Desargues' theorem, and show the result is the converse of Desargues' theorem.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| desargues-theorem | Direct parent — the theorem itself | Projective geometry, incidence |
| desargues-theorem-oq-02 | Moulton counterexample | Non-Desarguesian planes |

## Initial Thoughts

### Potential Approaches

1. **Axiomatic projective plane with duality**: Define IncidenceStructure with point/line types, define a Dual type that swaps them, show Desargues statement maps to its converse
   - Why it might work: Clean abstract approach
   - Risk: Need to carefully define "perspective from a point/line"

2. **Coordinate-based**: Work in a projective plane over a division ring, use matrix duality
   - Why it might work: Concrete and computable
   - Risk: Loses the synthetic beauty

### Key Difficulties

- Defining the duality transformation formally (it's a functor on the incidence structure)
- Stating Desargues' theorem in a form where duality is syntactically visible
- Handling the asymmetry between point-perspective and line-perspective

### What Would a Proof Need?

- Key lemma 1: Duality preserves incidence (point on line ↔ line through point)
- Key lemma 2: Dual of "concurrent lines" = "collinear points"
- Key lemma 3: Dual of "perspective from point" = "perspective from line"
- Technical requirements: Incidence geometry formalization

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The duality principle is conceptually clean
- Existing gallery proof provides the forward direction
- Main work is defining the duality transformation
- Once defined, the self-duality should follow by structural reasoning

## References

### Papers
- Coxeter, "Projective Geometry" (duality principle, Ch. 14)
- Hilbert & Cohn-Vossen, "Geometry and the Imagination"

### Mathlib
- `Mathlib.Combinatorics.Configuration` — incidence structures
- `Mathlib.LinearAlgebra.ProjectiveSpace` — projective spaces

## Metadata

```yaml
tags:
  - geometry
  - projective-geometry
  - duality
  - incidence
related_proofs:
  - desargues-theorem
  - desargues-theorem-oq-02
difficulty: medium
source: gallery-gap
created: 2026-03-11
```
