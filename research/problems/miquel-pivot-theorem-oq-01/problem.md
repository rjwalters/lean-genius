# Problem: Miquel's Pivot Theorem

**Slug**: miquel-pivot-theorem-oq-01
**Created**: 2026-06-16T06:31:45-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $ABC$ be a triangle, and let $X, Y, Z$ be points lying on lines $BC$,
$CA$, $AB$ respectively. Then the three circles
$$
\odot(AZY), \quad \odot(BXZ), \quad \odot(CYX)
$$
pass through a common point $M$, the *Miquel point* of $X, Y, Z$ with respect
to $\triangle ABC$.

$$
\exists\, M, \quad M \in \odot(AZY) \cap \odot(BXZ) \cap \odot(CYX).
$$

### Plain Language

Pick one point on each side of a triangle. For each vertex, draw the circle
through that vertex and the two chosen points on the adjacent sides. The three
circles you get always meet at a single common point.

### Why This Matters

Miquel's theorem (the "pivot theorem") is a fundamental concurrency result in
circle geometry, generalizing to the Miquel point of a complete quadrilateral
and underlying spiral-similarity arguments used throughout olympiad and
classical geometry. Formalizing it builds out Mathlib's circle/concyclicity
toolkit and pairs naturally with the gallery's existing concurrency proofs.

## Known Results

### What's Already Proven

- Concyclicity / cospherical predicates — `EuclideanGeometry.Cospherical`,
  `EuclideanGeometry.Concyclic`, and `Sphere` API (Mathlib).
- Directed angles and the concyclicity ⇔ equal-directed-angle criterion —
  `EuclideanGeometry.oangle`, `Cospherical` ↔ `oangle` lemmas (Mathlib).

### What's Still Open

- No formalization of Miquel's pivot theorem in Mathlib or the gallery.
- Stronger forms (Miquel point of a complete quadrilateral, spiral-similarity
  characterization, six-circle theorem) are all unformalized.

### Our Goal

Formalize the base pivot theorem: define $M$ as the second intersection of
two of the circles, then show $M$ lies on the third. The complete-quadrilateral
and spiral-similarity generalizations are out of scope (future OQs).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| pascals-hexagon | Concurrency/incidence on conics and circles | projective/circle incidence |
| ptolemys-theorem | Concyclicity criterion in complex coordinates | complex numbers |
| cevas-theorem | Concurrency from ratios on triangle sides | ratio/area arguments |

## Initial Thoughts

### Potential Approaches

1. **Directed-angle concyclicity criterion**: Define $M$ as the second
   intersection of $\odot(AZY)$ and $\odot(BXZ)$. Use the directed-angle
   characterization of concyclicity ($\angle(MX, MY) = \angle(CX, CY)$ as
   directed angles mod $\pi$) and angle-chasing to show $M, X, Y, C$ concyclic.
   - Why it might work: Mathlib's `oangle` mod-$\pi$ machinery is exactly the
     tool for "concyclic iff equal directed angles."
   - Risk: defining the *second* intersection point and its existence cleanly.

2. **Complex-number coordinates**: Represent points as complex numbers; a
   circle through three points and concyclicity become cross-ratio reality
   conditions. The common-point claim reduces to consistency of two circle
   equations and an algebraic identity.
   - Why it might work: aligns with successful turnkey complex-coordinate
     gallery proofs; concyclicity = real cross-ratio.
   - Risk: handling existence/uniqueness of the intersection algebraically.

### Key Difficulties

- Constructing the Miquel point $M$ (second intersection of two circles) and
  proving it exists/well-defined before showing it lies on the third circle.
- Degenerate configurations (chosen points coinciding with vertices, collinear
  triples) must be excluded by hypotheses.

### What Would a Proof Need?

- A clean definition of "second intersection of two circles."
- The directed-angle concyclicity criterion in usable Mathlib form, or the
  complex cross-ratio reality condition.
- An angle-chase / algebraic identity closing the third concyclicity.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Concyclicity and directed-angle tools exist in Mathlib; the proof is a
  standard angle-chase once $M$ is defined.
- Slightly harder than the pure-identity coordinate theorems (Varignon, British
  Flag) because it requires constructing an intersection point.

**Estimated Effort**:
- Exploration: hours to 1 day
- If tractable: 2–4 days
- If hard: 1–2 weeks (if existence of $M$ proves awkward in Mathlib)

## References

### Papers
- Classical; see Coxeter & Greitzer, *Geometry Revisited* (1967), §3.7
  (Miquel point and the pivot theorem).

### Online Resources
- https://en.wikipedia.org/wiki/Miquel%27s_theorem — statement and proofs.

### Mathlib
- `Mathlib.Geometry.Euclidean.Sphere.Basic` (circles, concyclicity).
- `Mathlib.Geometry.Euclidean.Angle.Oriented` (directed angles mod π).
- `Mathlib.Geometry.Euclidean.Sphere.SecondInter` (second intersection of a line/sphere).

## Metadata

```yaml
tags:
  - euclidean-geometry
  - triangle-geometry
  - circle-geometry
  - concurrency
related_proofs:
  - pascals-hexagon
  - ptolemys-theorem
  - cevas-theorem
difficulty: medium
source: gallery-gap
created: 2026-06-16T06:31:45-07:00
```
