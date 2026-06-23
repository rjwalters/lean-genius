# Problem: Ceva's Theorem for Spherical Polygons

**Slug**: cevas-theorem-oq-02-oq-02
**Created**: 2026-03-06
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a spherical n-gon P₁P₂...Pₙ with generalized cevians from each vertex Pᵢ to a point Qᵢ on the opposite side, the cevians concur if and only if:

$$
\prod_{i=1}^{n} \frac{\sin(\angle P_i C Q_i)}{\sin(\angle Q_i C P_{i+1})} = 1
$$

where C is the center of the sphere and angles are measured in the tangent plane.

### Plain Language

Ceva's theorem tells us when lines from the vertices of a triangle through points on opposite sides all meet at one point. We want to generalize this to polygons (quadrilaterals, pentagons, etc.) on a sphere.

### Why This Matters

Spherical geometry is fundamental in navigation, astronomy, and computational geometry. Extending classical concurrence theorems to spherical polygons connects Euclidean intuition with non-Euclidean reality.

## Known Results

### What's Already Proven

- Ceva's theorem for spherical triangles — `cevas-theorem-oq-02` (gallery, with Gauss-Bonnet)
- Euclidean Ceva for triangles — classical Mathlib
- Routh's theorem for Euclidean triangles — ratio-based generalization

### What's Still Open

- Cevian concurrence for spherical n-gons (n ≥ 4)
- Correct definition of "generalized cevian" in polygons
- Connection to spherical excess/area

### Our Goal

Formalize the cevian concurrence condition for spherical quadrilaterals (n=4) as a first step, then generalize.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cevas-theorem-oq-02 | Spherical/hyperbolic Ceva | Sine ratios, Gauss-Bonnet |
| cevas-theorem | Euclidean Ceva | Ratio products |

## Initial Thoughts

### Potential Approaches

1. **Start with n=4**: Prove cevian concurrence for spherical quadrilaterals, then inductively extend
   - Why it might work: Quadrilateral case is concrete and testable
   - Risk: The formula may not simply generalize by induction

2. **Projective approach**: Use the spherical-projective duality to reduce to projective Ceva
   - Why it might work: Projective geometry unifies Euclidean/spherical
   - Risk: Mathlib projective geometry support may be limited

### Key Difficulties

- Defining "opposite side" in an n-gon (not well-defined for n > 3)
- Choosing the right generalization (diagonal cevians vs edge cevians)
- Spherical trigonometry in Lean 4

### What Would a Proof Need?

- Key lemma 1: Spherical sine rule for triangles (may exist from gallery proof)
- Key lemma 2: Triangulation of spherical n-gon
- Key lemma 3: Product formula for concatenated sine ratios
- Technical requirements: Spherical geometry primitives

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- Spherical triangle case already proven in gallery
- The n-gon generalization requires careful geometric definitions
- Limited literature on exactly this formulation

## References

### Papers
- Grünbaum & Shephard, "Ceva, Menelaus, and the Area Principle" — generalized concurrence

### Mathlib
- `Geometry.Euclidean` — Euclidean geometry primitives
- Gallery proof `cevas-theorem-oq-02` — spherical infrastructure to reuse

## Metadata

```yaml
tags:
  - geometry
  - non-euclidean
  - spherical-geometry
  - concurrency
  - cevians
  - polygons
related_proofs:
  - cevas-theorem-oq-02
  - cevas-theorem
difficulty: medium-high
source: gallery-gap
created: 2026-03-06
```

**Significance**: 7/10
**Tractability**: 6/10
