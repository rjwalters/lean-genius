# Problem: de Gua's Theorem — the Three-Dimensional Pythagorean Theorem

**Slug**: pythagorean-theorem-oq-06
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
A_0^2 \;=\; A_1^2 + A_2^2 + A_3^2,
$$

where, for a tetrahedron with a trirectangular vertex (three mutually perpendicular edges at one vertex), $A_0$ is the area of the face opposite that vertex and $A_1, A_2, A_3$ are the areas of the three mutually perpendicular faces.

### Plain Language

The Pythagorean theorem relates the squared length of the hypotenuse to the squared lengths of the two legs of a right triangle. de Gua's theorem is its exact three-dimensional analogue: take a tetrahedron that has a "right-angle corner," where three faces meet at mutually perpendicular edges (like the corner of a box). Then the square of the area of the slanted face opposite that corner equals the sum of the squares of the areas of the three perpendicular faces. The classical Pythagorean theorem is recovered by collapsing one dimension.

### Why This Matters

The gallery treats the Pythagorean theorem as a planar fact. de Gua's theorem shows the "sum of squares" identity is dimension-agnostic: it is the n = 3 case of a general n-simplex theorem (the squared (n−1)-volume of the hypotenuse face equals the sum of squared volumes of the legs). Formalizing it connects elementary triangle area to Gram determinants and projected areas in EuclideanSpace, and provides a clean, self-contained target that generalizes a flagship gallery result into higher dimensions.

## Known Results

### What's Already Proven

- `pythagorean-theorem` — the 2D right-triangle case this generalizes, already in the gallery.
- Mathlib provides `EuclideanSpace`, inner products, cross products in ℝ³ (`crossProduct`), and triangle-area infrastructure usable to define face areas.

### What's Still Open

- A formal definition of the trirectangular tetrahedron and its four face areas in ℝ³.
- The identity A₀² = A₁² + A₂² + A₃².
- The general n-simplex extension (sum of squared facet volumes), via Gram determinants.

### Our Goal

Formalize de Gua's theorem in Euclidean ℝ³: define the three perpendicular faces and the opposite face of a trirectangular tetrahedron, and prove A₀² = A₁² + A₂² + A₃². A natural route expresses each perpendicular face area as a coordinate projection of the opposite face (areas are 1/2·‖cross product‖) and reduces the claim to ‖u×v‖² decomposition. Then note the Gram-determinant form that extends to general n.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| pythagorean-theorem | The 2D case this generalizes | inner products, orthogonality |
| herons-formula | Triangle face areas from edge data | area formulas |
| greens-theorem | Oriented area / projection viewpoint | vector calculus, projected areas |

## Initial Thoughts

### Potential Approaches

1. **Approach A (cross-product projection)**: Place the right-angle vertex at the origin with legs along the axes; write the opposite-face area as ½‖u×v‖ and the three perpendicular-face areas as the coordinate components of u×v.
   - Why it might work: A₀² = ¼‖u×v‖² = ¼((u×v)₁² + (u×v)₂² + (u×v)₃²), and each component squared is exactly the squared area of a perpendicular face.
   - Risk: matching the component-area identification and the ½ factors precisely.

2. **Approach B (Gram determinant)**: Express each face area via a 2×2 Gram determinant and expand; this generalizes directly to the n-simplex statement.
   - Why it might work: uniform, dimension-independent; reuses determinant lemmas.
   - Risk: more abstract; heavier Mathlib determinant plumbing for a 3D result.

### Key Difficulties

- Defining face areas consistently (½‖cross product‖) and identifying the coordinate-plane projections with the perpendicular faces.
- Keeping the ½ and squared factors exact through the ‖u×v‖² decomposition.

### What Would a Proof Need?

- Key lemma 1: ‖u×v‖² = (u×v)₁² + (u×v)₂² + (u×v)₃² (just the norm in ℝ³).
- Key lemma 2: each perpendicular face area equals ½ times one coordinate of |u×v| (projection onto a coordinate plane).
- Technical requirements: `crossProduct` in ℝ³, `EuclideanSpace` norms, triangle area as ½‖cross product‖.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The ℝ³ case reduces to a one-line norm decomposition once areas are set up via the cross product, so the work is mostly definitional plumbing.
- The Pythagorean and triangle-area pieces are already in the gallery/Mathlib.
- Mathlib has cross products, inner products, and Euclidean norms in ℝ³.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1 week
- If hard: unknown (clean general n-simplex form)

## References

### Papers
- J. P. de Gua de Malves (1783) — classical statement of the three-square theorem.
- E. W. Beyer / Conant–Beyer — the general n-simplex "Pythagorean" generalization (sum of squared facet volumes).

### Online Resources
- de Gua's theorem, Wikipedia — statement, the cross-product proof, and the n-simplex generalization.

### Mathlib
- `Mathlib.Analysis.InnerProductSpace.PiL2` (`EuclideanSpace`) — norms and inner products in ℝ³.
- `Mathlib.LinearAlgebra.CrossProduct` — cross product and `‖u×v‖` for face areas.

## Metadata

```yaml
tags:
  - geometry
  - euclidean-space
  - pythagorean
related_proofs:
  - pythagorean-theorem
  - herons-formula
difficulty: medium
source: gallery-gap
created: 2026-06-16
```
