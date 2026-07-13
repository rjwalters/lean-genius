# Problem: Brianchon's Theorem

**Slug**: brianchon-theorem-oq-01
**Created**: 2026-06-16T06:50:00-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let a hexagon $A_1 A_2 A_3 A_4 A_5 A_6$ be circumscribed about a conic (each of
its six sides is tangent to the conic). Then the three main diagonals
$A_1A_4$, $A_2A_5$, $A_3A_6$ are concurrent. This point is the *Brianchon
point*. Brianchon's theorem is the projective dual of Pascal's theorem.

### Plain Language

If a six-sided figure has all six sides touching a single conic (e.g. a
circle), then the three long diagonals connecting opposite corners all pass
through one common point.

### Why This Matters

Brianchon's theorem is the projective dual of Pascal's hexagon theorem — which
is already in the gallery (`pascals-hexagon`). Formalizing it completes the
classic Pascal/Brianchon duality pair and exercises Mathlib's projective and
conic/duality infrastructure (or a direct coordinate/pole–polar argument).

## Known Results

### What's Already Proven

- Pascal's hexagon theorem is formalized in the gallery (`pascals-hexagon`,
  `PascalsHexagon.lean`) — the dual statement.
- Projective plane / duality and conic API in Mathlib
  (`Mathlib.LinearAlgebra.Projectivization`, projective duality).

### What's Still Open

- No formalization of Brianchon's theorem in Mathlib or the gallery.
- A clean dualization bridge from the gallery's Pascal proof is unformalized.

### Our Goal

Formalize Brianchon's theorem, ideally by dualizing the existing Pascal proof
via pole–polar duality with respect to the conic, or directly via a
coordinate/projective concurrency computation for the circle case.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| pascals-hexagon | Exact projective dual statement | projective incidence |
| ptolemys-theorem | Circle/conic incidence relations | complex/metric |
| desargues-theorem | Projective concurrency/collinearity duality | projective geometry |

## Initial Thoughts

### Potential Approaches

1. **Pole–polar dualization of Pascal**: Apply the polarity induced by the
   conic. Tangent lines (sides of the circumscribed hexagon) dualize to the
   points of contact lying on the conic; the Pascal line of those points
   dualizes to the Brianchon concurrency point. Reuse `pascals-hexagon`.
   - Why it might work: leverages an already-formalized result; conceptually
     short.
   - Risk: building the polarity/duality map and the contact-point
     correspondence formally in Mathlib may be heavy.

2. **Direct coordinate proof for the circle**: Specialize to a hexagon
   circumscribed about a circle, parametrize tangent points by angles, compute
   the three diagonals, and show concurrency by a determinant/`ring` identity.
   - Why it might work: avoids building duality; reduces to algebra.
   - Risk: only covers the circle (not a general conic); messy parametrization.

### Key Difficulties

- Formalizing projective duality / the pole–polar map cleanly, or
- Managing the algebraic concurrency computation and tangency conditions.
- Degenerate configurations (coincident tangent points, parallel diagonals at
  infinity) require projective treatment.

### What Would a Proof Need?

- A usable conic + tangency formalization, or a circle parametrization.
- The pole–polar duality bridge to Pascal, or a determinant concurrency lemma.
- Handling of points at infinity (projective closure).

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- The dual statement (Pascal) is already formalized, suggesting a path, but
  projective duality in Mathlib is non-trivial to wield.
- The circle-only coordinate route is more tractable but less general.

**Estimated Effort**:
- Exploration: 1 day
- If tractable (circle coordinate route): 3–5 days
- If hard (full conic duality): 1–3 weeks

## References

### Papers
- C. J. Brianchon (1810); see Coxeter, *Projective Geometry*.

### Online Resources
- https://en.wikipedia.org/wiki/Brianchon%27s_theorem — statement, duality with Pascal.

### Mathlib
- `Mathlib.LinearAlgebra.Projectivization.Basic` (projective space).
- `Mathlib.Geometry.Euclidean.Sphere.Basic` (circle, tangency for the circle case).
- Gallery `PascalsHexagon.lean` (the dual theorem to reuse).

## Metadata

```yaml
tags:
  - projective-geometry
  - conics
  - duality
related_proofs:
  - pascals-hexagon
  - desargues-theorem
  - ptolemys-theorem
difficulty: hard
source: gallery-gap
created: 2026-06-16T06:50:00-07:00
```
