# Problem: Simson Line Theorem

**Slug**: simson-line-theorem-oq-01
**Created**: 2026-06-16T06:31:45-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $ABC$ be a triangle and $P$ a point. Let $X, Y, Z$ be the feet of the
perpendiculars from $P$ onto lines $BC$, $CA$, $AB$ respectively. Then
$X, Y, Z$ are collinear **if and only if** $P$ lies on the circumcircle of
$ABC$. The line $XYZ$ is the *Simson line* (or Wallace line) of $P$.

$$
P \in \odot(ABC) \iff \operatorname{collinear}\{X, Y, Z\}.
$$

### Plain Language

Drop perpendiculars from a point $P$ to the three sides of a triangle. The
three feet of those perpendiculars line up on a single straight line exactly
when $P$ sits on the triangle's circumscribed circle.

### Why This Matters

The Simson line is a cornerstone of classical triangle geometry, connecting
the circumcircle to a family of remarkable lines (its envelope is a deltoid;
the Simson lines of antipodal points are perpendicular). It is a natural,
self-contained target that exercises Mathlib's Euclidean-geometry and
orthogonal-projection API, and complements existing circle/triangle proofs in
the gallery.

## Known Results

### What's Already Proven

- Foot-of-perpendicular / orthogonal projection onto an affine subspace —
  `EuclideanGeometry.orthogonalProjection` (Mathlib).
- Concyclicity and the inscribed-angle machinery — `EuclideanGeometry.Sphere`,
  `Cospherical`, `oangle` (directed angles) in Mathlib.
- Collinearity predicate — `Collinear ℝ {X, Y, Z}` (Mathlib).

### What's Still Open

- No formalization of the Simson line theorem appears in Mathlib or the gallery.
- The biconditional (collinearity $\iff$ concyclic) and the deltoid envelope are
  both unformalized.

### Our Goal

Formalize the core biconditional: the three pedal feet of $P$ w.r.t. triangle
$ABC$ are collinear iff $P$ is concyclic with $A, B, C$. The deltoid envelope
and antipodal-perpendicularity are out of scope (future OQs).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| ptolemys-theorem | Concyclicity criterion via complex/metric identities | complex numbers, metric geometry |
| feuerbachs-theorem | Pedal/contact geometry on a triangle | coordinate + circle geometry |
| napoleons-theorem | Triangle construction proved with complex coordinates | complex-number coordinates |

## Initial Thoughts

### Potential Approaches

1. **Directed-angle (Mathlib `oangle`) approach**: Use the fact that pairs of
   pedal feet are concyclic with $P$ and a vertex (right angles subtend a
   diameter), then chase directed angles to force collinearity exactly when
   $P$ is on the circumcircle.
   - Why it might work: Mathlib has a substantial directed-angle library
     (`EuclideanGeometry.oangle`, `Sphere.oangle_eq` style lemmas).
   - Risk: directed-angle bookkeeping is fiddly; orientation hypotheses.

2. **Complex-number coordinates**: Place the circumcircle as the unit circle,
   $A, B, C, P$ on $|z| = 1$. The foot of the perpendicular from $P$ to chord
   $AB$ has a closed form $\tfrac12(a + b + p - ab\bar p)$; collinearity of the
   three feet reduces to a polynomial identity that holds iff $|p| = 1$.
   - Why it might work: mirrors the successful turnkey complex-coordinate
     proofs (Varignon, British Flag, van Aubel) — reduces to a
     `linear_combination`/`ring` identity.
   - Risk: the general off-circle direction needs the converse handled too.

### Key Difficulties

- Stating "foot of perpendicular onto a line" cleanly and connecting it to the
  closed-form chord-foot formula.
- The converse direction (collinear $\Rightarrow$ concyclic) requires ruling
  out the degenerate/off-circle case.

### What Would a Proof Need?

- Closed form for the pedal foot of $P$ onto a chord of the unit circle.
- A collinearity criterion (e.g. the imaginary part of a cross-ratio / a
  determinant vanishing) in complex coordinates.
- The algebraic identity reducing collinearity to $p\bar p = 1$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Strongly analogous to already-completed turnkey complex-coordinate triangle
  theorems in the gallery (Varignon, British Flag, van Aubel, Viviani).
- The forward direction reduces to a single algebraic identity; the converse is
  the only genuinely new piece.
- Mathlib provides orthogonal projection, collinearity, and concyclicity APIs.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days
- If hard: 1 week (if forced onto the synthetic directed-angle route)

## References

### Papers
- Classical; see Coxeter & Greitzer, *Geometry Revisited* (1967), §2.5.

### Online Resources
- https://en.wikipedia.org/wiki/Simson_line — statement, proof sketches, deltoid envelope.

### Mathlib
- `Mathlib.Geometry.Euclidean.Projection` (orthogonal projection / feet of perpendiculars).
- `Mathlib.Geometry.Euclidean.Angle.Oriented` (directed angles).
- `Mathlib.Geometry.Euclidean.Sphere.Basic` (circumcircle, concyclicity).

## Metadata

```yaml
tags:
  - euclidean-geometry
  - triangle-geometry
  - coordinate-geometry
  - circle-geometry
related_proofs:
  - ptolemys-theorem
  - feuerbachs-theorem
  - napoleons-theorem
difficulty: medium
source: gallery-gap
created: 2026-06-16T06:31:45-07:00
```
