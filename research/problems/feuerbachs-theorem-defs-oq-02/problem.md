# Problem: Nine-Point Circle Uniqueness

**Slug**: feuerbachs-theorem-defs-oq-02
**Created**: 2026-04-05T17:45:36-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For any non-degenerate triangle ABC, the nine-point circle is the unique circle
passing through the 9 special points: 3 side midpoints, 3 altitude feet, 3 Euler
midpoints (vertex-to-orthocenter midpoints).

More precisely: if a circle Γ passes through the midpoints of the three sides of
triangle ABC, then Γ is the nine-point circle (center = midpoint(O, H), radius = R/2),
because three non-collinear points uniquely determine a circle.

### Plain Language

The gallery proof (`feuerbachs-theorem-defs`) already establishes that all 9 special
points lie on the nine-point circle. OQ-02 asks: prove the nine-point circle is the
*only* circle with this property. This reduces to showing that at least 3 of the 9
points are non-collinear, then applying the uniqueness theorem for circles through 3
non-collinear points.

### Why This Matters

Uniqueness makes the nine-point circle a canonical geometric object rather than just
a convenient one. Without uniqueness, "the nine-point circle" is just "a circle
through these points." The uniqueness proof completes the definitional picture for
Wiedijk #29 in the gallery.

## Known Results

### What's Already Proven

- `feuerbachs-theorem-defs`: All 9 special points lie on the nine-point circle
  (VERIFIED, 0 sorries)
- `feuerbachs-theorem-oq-01`: Complete distance relations (VERIFIED)
- Mathlib: Circumsphere/circumcenter uniqueness infrastructure exists

### What's Still Open

- That at least 3 of the 9 special points are non-collinear in a non-degenerate triangle
- Formal statement of uniqueness in the coordinate framework used in FeuerbachsTheoremDefs

### Our Goal

Prove: for a non-degenerate triangle, the three side midpoints are non-collinear, so
any circle through all 9 special points must be the nine-point circle.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| feuerbachs-theorem-defs | Infrastructure: 9 membership proofs, coordinate framework | Coordinate geometry, R^2 arithmetic |
| feuerbachs-theorem | Main tangency theorem | Circle tangency in coordinates |
| feuerbachs-theorem-oq-05 | Inversive geometry proof | Alternative proof framework |

## Initial Thoughts

### Potential Approaches

1. **Non-collinearity of midpoints**: The midpoints of the three sides of a
   non-degenerate triangle are non-collinear. Prove this in coordinates (det ≠ 0
   via the triangle area formula). Then invoke a Mathlib lemma that 3 non-collinear
   points determine a unique sphere/circle.
   - Why it might work: Direct coordinate computation.
   - Risk: May need to find the right Mathlib API for circle uniqueness in the plane.

2. **Equidistance system uniqueness**: Show that the system of equations (center
   equidistant from 3 non-collinear points) has a unique solution. Since
   FeuerbachsTheoremDefs already computes the nine-point center N = midpoint(O, H)
   and radius R/2, this is a verification that the system has exactly one solution.
   - Why it might work: Linear algebra — the perpendicular bisectors of 3 sides of
     a non-degenerate triangle meet in exactly one point.
   - Risk: May require extra linear algebra lemmas.

### Key Difficulties

- Finding the correct Mathlib API for "3 non-collinear points → unique circle"
- The existing code uses coordinate geometry (not Mathlib's abstract EuclideanGeometry),
  so abstract sphere uniqueness lemmas may need adaptation

### What Would a Proof Need?

- Key lemma: The three side midpoints of a non-degenerate triangle are non-collinear
- Key theorem: Three non-collinear points lie on exactly one circle
- Technical: Connecting FeuerbachsTheoremDefs' coordinate framework to Mathlib's API

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- Mathematical content is straightforward (non-collinearity + circle uniqueness)
- The existing coordinate infrastructure in FeuerbachsTheoremDefs is comprehensive
- Main challenge is Mathlib API discovery
- Should be achievable without sorries

**Estimated Effort**:
- Exploration: 1-2 hours (API search + non-collinearity proof sketch)
- If tractable: 1-2 days

## References

### Mathlib
- `Mathlib.Geometry.Euclidean.Sphere.Basic` — Sphere definitions
- `Mathlib.Geometry.Euclidean.Circumcenter` — Circumcenter uniqueness
- `EuclideanGeometry.circumsphere` — Abstract circumsphere

## Metadata

```yaml
tags:
  - geometry
  - euclidean-geometry
  - nine-point-circle
  - feuerbach
  - uniqueness
  - triangle
related_proofs:
  - feuerbachs-theorem-defs
  - feuerbachs-theorem
  - feuerbachs-theorem-oq-01
difficulty: low-medium
source: gallery-gap
created: 2026-04-05T17:45:36-07:00
```
