# Problem: Dual Spherical Law of Cosines

**Slug**: spherical-law-of-sines-oq-02
**Created**: 2026-04-05T13:56:47-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a spherical triangle with sides $a, b, c$ (great-circle arcs in radians) and
opposite angles $A, B, C$, the dual spherical law of cosines states:

$$\cos C = -\cos A \cos B + \sin A \sin B \cos c$$

This complements the standard spherical law of cosines:
$$\cos c = \cos a \cos b + \sin a \sin b \cos C$$

### Plain Language

On a sphere, triangles satisfy two "laws of cosines": one expressing a side in terms
of the other two sides and the opposite angle, and a dual version expressing an angle
in terms of the other two angles and the opposite side. The gallery has the spherical
law of sines; this problem asks for the dual law of cosines, completing the spherical
trigonometry picture.

### Why This Matters

Completes the classical spherical trigonometry suite in Lean's gallery. Together with
the law of sines, it gives all tools needed to solve spherical triangles. Applications:
celestial navigation, geodesy, computer graphics on $S^2$.

## Known Results

### What's Already Proven

- Spherical law of sines — `spherical-law-of-sines` (gallery)
- (Standard) spherical law of cosines is closely related to the law of sines proof

### What's Still Open

- Lean formalization of the dual spherical law of cosines

### Our Goal

Prove `cos C = -cos A * cos B + sin A * sin B * cos c` in Lean 4 for a spherical
triangle, using the infrastructure from `spherical-law-of-sines`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| spherical-law-of-sines | Direct parent; sets up spherical geometry | Cross-product, dot-product on S² |

## Initial Thoughts

### Potential Approaches

1. **Via polar (dual) triangle**: Apply the standard spherical law of cosines to the
   polar triangle (where sides and angles swap roles). Then translate back.
   - Why it might work: Textbook proof; polar triangle duality is clean algebra.
   - Risk: Requires formalizing the polar triangle construction in Lean.

2. **Direct vector computation**: Using unit vectors $\mathbf{a}, \mathbf{b}, \mathbf{c}$
   on $S^2$, express $\cos C$ as $\cos(\angle(\mathbf{a}\times\mathbf{b}, \mathbf{a}\times\mathbf{c}))$
   and expand using dot/cross product identities.
   - Why it might work: The parent proof likely uses vectors; extend the same setup.
   - Risk: Angle computation for normals to great circles needs care.

3. **From the standard law**: The dual law follows algebraically from the standard law
   via the spherical excess formula $E = A + B + C - \pi$.
   - Risk: Requires spherical excess; adds intermediate steps.

### Key Difficulties

- First need to read `proofs/Proofs/SphericalLawOfSines.lean` to understand what
  definitions are in place (angle type, side type, triangle hypothesis)
- Polar triangle duality may need new definitions

### What Would a Proof Need?

- Read: `proofs/Proofs/SphericalLawOfSines.lean` — understand existing setup
- Key lemma: standard spherical law of cosines (may already be proven as a step)
- Technical: `inner_cross_product_eq` or similar in `EuclideanSpace ℝ (Fin 3)`

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Clean extension of an existing gallery proof with established infrastructure
- Standard spherical trigonometry; well-understood mathematics
- Lean has `EuclideanSpace ℝ (Fin 3)` with dot and cross products

**Estimated Effort**:
- Exploration: 1 day (read parent proof structure in detail)
- If tractable: 3-7 days for complete proof

## References

### Papers
- Todhunter, I. (1886) — "Spherical Trigonometry" (classical treatment)

### Mathlib
- `Mathlib.Analysis.InnerProductSpace.Basic` — dot products
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` — trig functions
- `Mathlib.Geometry.Euclidean.Basic` — Euclidean geometry in Lean

## Metadata

```yaml
tags:
  - geometry
  - spherical-geometry
  - trigonometry
  - non-euclidean-geometry
related_proofs:
  - spherical-law-of-sines
difficulty: medium
source: gallery-gap
created: 2026-04-05T13:56:47-07:00
```

**Significance**: 6/10
**Tractability**: 5/10
