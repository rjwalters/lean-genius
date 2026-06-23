# Problem: Viviani's Theorem — Sum of Distances in an Equilateral Triangle

**Slug**: viviani-theorem-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: seeker-selected <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
d_a + d_b + d_c = h
$$

For an equilateral triangle with side length $s$ and altitude $h = \frac{\sqrt3}{2}s$,
and any point $P$ inside (or on) the triangle, the sum of the perpendicular distances
$d_a, d_b, d_c$ from $P$ to the three sides equals the altitude $h$, independent of the
position of $P$.

### Plain Language

Stand anywhere inside an equilateral triangle and measure your straight-line distance
to each of the three sides. No matter where you stand, those three distances always add
up to the same number — the height of the triangle. The position of the point does not
matter at all.

### Why This Matters

Viviani's theorem (Vincenzo Viviani, 17th century) is a classic, visually appealing
invariance result whose cleanest proof is an area-decomposition argument: the three
triangles $PBC, PCA, PAB$ tile the whole triangle, so $\frac12 s\,d_a + \frac12 s\,d_b
+ \frac12 s\,d_c = \frac12 s\,h$, giving $d_a + d_b + d_c = h$ after cancelling
$\frac12 s$. It is a named theorem with no current gallery entry and is an excellent
test of formalizing Euclidean-geometry area/distance reasoning in Mathlib.

## Known Results

### What's Already Proven

- Mathlib has `EuclideanGeometry`, `Metric` distances, `EuclideanGeometry.dist` to a
  line/affine subspace via `EuclideanGeometry.orthogonalProjection`, and triangle area
  via `MeasureTheory.volume` of a convex hull or via the `1/2 · base · height` shoelace
  form (`EuclideanGeometry.oangle`/`Affine.Triangle` helpers, `MeasureTheory` convex
  body volume).
- The additivity of area over a partition of the triangle into three sub-triangles
  sharing the interior point $P$ is the crux; area as $\frac12 \cdot \text{base} \cdot
  \text{height}$ is the key identity.

### What's Still Open

- No Lean formalization of Viviani's theorem exists in this gallery.
- The area-decomposition identity $[PBC] + [PCA] + [PAB] = [ABC]$ for an interior $P$,
  expressed with perpendicular distances, has not been assembled here.

### Our Goal

Formalize Viviani's theorem for an equilateral triangle in the Euclidean plane
($\mathbb{R}^2$ or `EuclideanSpace ℝ (Fin 2)`): for any $P$ in the (closed) triangle,
the sum of perpendicular distances from $P$ to the three sides equals the altitude.
Prove it via the area-decomposition identity and the equal-side-length hypothesis.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| picks-theorem | Area reasoning for planar polygons | lattice/area decomposition, `MeasureTheory` |
| morley-theorem | Euclidean-triangle geometry in Mathlib | `EuclideanGeometry`, angles, distances |
| ptolemy | Distance identities in planar configurations | `dist`, inner-product geometry |

## Initial Thoughts

### Potential Approaches

1. **Area decomposition**: write $[ABC] = [PBC] + [PCA] + [PAB]$ for interior $P$, use
   $[XYZ] = \frac12 \cdot (\text{side}) \cdot (\text{distance from opposite vertex})$,
   factor out the common side length $s$, and cancel.
   - Why it might work: it is the standard one-line proof; reduces to area additivity
     plus the base-times-height formula, both available in Mathlib.
   - Risk: choosing a workable area definition (signed area / shoelace vs.
     `MeasureTheory.volume`) and proving additivity of the partition cleanly.

2. **Coordinate / barycentric computation**: place the triangle with explicit
   coordinates, compute the three distances and sum them algebraically.
   - Why it might work: fully computational; `ring`/`nlinarith` can close it.
   - Risk: less elegant and ties the result to a specific embedding; still a valid
     fallback if the synthetic area route is fiddly.

### Key Difficulties

- Selecting the right Mathlib notion of "perpendicular distance from a point to a side"
  (`EuclideanGeometry.orthogonalProjection` / `Metric.infDist` to the affine span) and
  relating it to a base-times-height area expression.
- Establishing additivity of area over the three-piece partition for an interior point.

### What Would a Proof Need?

- Key lemma 1: triangle area equals $\frac12 \cdot |\text{base}| \cdot
  \text{dist}(\text{apex}, \text{base line})$.
- Key lemma 2: area additivity $[ABC] = [PBC] + [PCA] + [PAB]$ for $P$ in the triangle.
- Technical requirements: `EuclideanGeometry`, `EuclideanGeometry.orthogonalProjection`,
  an area/`volume` API, and the equilateral hypothesis $|AB| = |BC| = |CA| = s$.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- The mathematics is elementary (one area-decomposition identity), and a coordinate
  fallback can discharge it with `ring`/`nlinarith` if the synthetic route stalls.
- Adjacent gallery proofs (picks-theorem, morley-theorem, ptolemy) already exercise the
  planar-geometry and area machinery this needs.

**Estimated Effort**:
- Exploration: half a day
- If tractable: 2 to 4 days
- If hard: 1 week (only if a clean Mathlib area-additivity lemma is hard to locate)

## References

### Papers
- V. Viviani, attributed 1659 — original observation.
- C. Alsina and R. B. Nelsen, "Charming Proofs", MAA, 2010 — the area-decomposition
  proof (and generalizations to equiangular polygons).

### Online Resources
- Wikipedia, "Viviani's theorem" — statement, area proof, and generalizations.

### Mathlib
- `Mathlib.Geometry.Euclidean.Basic` — Euclidean affine geometry, distances.
- `Mathlib.Geometry.Euclidean.Projection` / `orthogonalProjection` — perpendicular
  distance to a line.
- `Mathlib.Analysis.Convex.*` / `MeasureTheory` — area of a triangle as a convex body.

## Metadata

```yaml
tags:
  - euclidean-geometry
  - area
  - equilateral-triangle
  - invariance
related_proofs:
  - picks-theorem
  - morley-theorem
difficulty: low
source: seeker-selected
created: 2026-06-16
```
