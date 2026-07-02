# Problem: Sharp Viviani Generalization to Regular Polygons and the Regular n-Simplex

**Slug**: viviani-theorem-oq-01-oq-02
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion <!-- open question of the verified parent viviani-theorem-oq-01 -->

## Problem Statement

### Formal Statement

$$
\text{For a regular } n\text{-gon (resp. regular } n\text{-simplex) with apothem } a
\text{ (resp. inradius } r\text{), and any interior point } P,\ \sum_{i} d(P, F_i) = n\,a
\ (\text{resp. } (n+1)\,r),\ \text{independent of } P.
$$

### Plain Language

Viviani's theorem says the sum of the perpendicular distances from any interior point of an equilateral triangle to its three sides is constant (equal to the triangle's altitude). This problem asks for the *sharp* generalization: prove the analogous constant-sum statement for every regular polygon (sum of distances to the sides) and for the regular n-simplex in higher dimensions (sum of distances to the facets), and identify the exact value of the constant in each case.

### Why This Matters

Viviani's theorem is a clean instance of a distance-sum invariant that follows from an area/volume decomposition. Extending it to regular polygons and simplices tests whether the same "partition the region into cones over each face and sum the volumes" argument formalizes cleanly in Lean for arbitrary dimension, and it produces a reusable invariant (constant weighted distance sum for regular bodies) that other geometry entries can cite.

## Known Results

### What's Already Proven

- Viviani's theorem for the equilateral triangle — parent entry `viviani-theorem-oq-01` (verified, 0-axiom).
- The area-decomposition identity `[ABC] = sum of [P F_i]` for the triangle — used in the parent proof.

### What's Still Open

- The regular n-gon case with the explicit constant `n · apothem`.
- The regular n-simplex case with the explicit constant `(n+1) · inradius`.
- A dimension-uniform statement via the facet/volume decomposition.

### Our Goal

Formalize the constant-sum theorem for the regular n-gon (arbitrary n ≥ 3) via the "sum of triangle areas equals total area" decomposition, then the regular n-simplex via the analogous "sum of sub-simplex volumes equals total volume" argument, giving the sharp constant in both.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| viviani-theorem-oq-01 | Direct parent; triangle case and area-decomposition template | area decomposition, EuclideanGeometry |
| napoleons-theorem-oq-04 | Sibling planar-geometry invariant proved by area accounting | area additivity |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Area/volume decomposition (recommended)**: partition the regular body into the cones/pyramids from the interior point P to each face; each has volume `(1/n) · (face measure) · d(P, F_i)`; summing recovers total volume, and since all faces are congruent the distance sum is forced to a constant.
   - Why it might work: it is exactly the parent's triangle argument, lifted by regularity (equal face measures).
   - Risk: Mathlib's higher-dimensional volume/facet API for simplices may be thin; may need to build the decomposition by hand.

2. **Approach B — Support-function / affine-functional argument**: express `d(P, F_i)` as an affine function of P; regularity makes the sum of the linear parts vanish, leaving a constant.
   - Why it might work: cleanly dimension-uniform.
   - Risk: setting up signed distances to facets in Lean is fiddly.

### Key Difficulties

- Higher-dimensional simplex volume and facet-inradius API in Mathlib.
- Handling "interior point" hypotheses (all signed distances nonnegative).

### What Would a Proof Need?

- Key lemma 1: volume of the pyramid from P to a facet = (1/n) · facetMeasure · d(P, facet).
- Key lemma 2: congruence of faces of a regular n-gon / n-simplex (equal measures).
- Technical requirements: `EuclideanGeometry`, `MeasureTheory` volume of simplices, affine subspaces.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The polygon case is a direct, low-risk extension of the verified triangle proof.
- The simplex case is the genuinely new content and may need hand-built volume decomposition.
- Recommend shipping the polygon case first (self-contained, high confidence), then attempting the simplex case.

**Estimated Effort**:
- Exploration: hours
- If tractable (polygon case): 1–3 days
- Simplex case: unknown (Mathlib support dependent)

## References

### Mathlib
- `Mathlib.Geometry.Euclidean.*` — Euclidean geometry, affine subspaces, distances.
- `Mathlib.Analysis.Convex.SimplicialComplex` / simplex volume — for the n-simplex case.

## Metadata

```yaml
tags:
  - geometry
  - euclidean-geometry
  - viviani
  - regular-polygon
  - simplex
related_proofs:
  - viviani-theorem-oq-01
  - napoleons-theorem-oq-04
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```
