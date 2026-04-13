# Problem: Extended Morley Theorem — Non-Adjacent Trisector Triangles

**Slug**: morleys-theorem-oq-02
**Created**: 2026-03-30
**Status**: Active
**Source**: gallery-gap (open question from morleys-theorem proof)

## Problem Statement

### Formal Statement

Morley's theorem states that the intersections of adjacent angle trisectors of any triangle form an equilateral triangle. The extended Morley theorem considers non-adjacent trisector pairs, which yield additional special triangles (18 Morley triangles total).

### Plain Language

When you trisect each angle of any triangle, the adjacent trisector lines meet to form a perfect equilateral triangle (Morley's theorem). But what about the non-adjacent trisector intersections? They form other special triangles with remarkable properties. Can we state and prove these extended results in Lean?

### Why This Matters

Morley's theorem is one of the most surprising results in elementary geometry. The extended version reveals a rich structure of 18 related triangles, connecting to projective geometry and the theory of cubic curves. Formalizing this would be a significant contribution to formalized geometry.

## Known Results

### What's Already Proven

- `morleys-theorem`: Morley's trisector theorem (verified, 0 axioms)
- The gallery proof uses coordinate geometry / trigonometric methods

### What's Still Open

- Classification of all 18 Morley triangles
- Which non-adjacent trisector combinations yield equilateral triangles
- Relationship between the 18 triangles

### Our Goal

State and prove at least one non-adjacent trisector result (e.g., the "second Morley triangle" from non-adjacent trisectors is also equilateral).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| morleys-theorem | Direct parent - adjacent trisector case | Trigonometric/coordinate geometry |
| feuerbachs-theorem | Triangle geometry infrastructure | Circle tangency, triangle centers |
| isosceles-triangle | Basic triangle geometry | Angle/side relationships |

## Initial Thoughts

### Potential Approaches

1. **Trigonometric extension**: Extend the existing Morley proof's coordinate framework to non-adjacent intersections
   - Why it might work: same techniques, different intersection points
   - Risk: computational complexity increases significantly

2. **Projective/algebraic approach**: Use the theory of cubic curves (the trisector lines lie on cubics)
   - Why it might work: more structural, may simplify
   - Risk: heavy algebraic geometry infrastructure needed

### Key Difficulties

- Identifying which of the 18 triangles to formalize first
- Trigonometric computation may be unwieldy
- Need to carefully define "non-adjacent" trisector pairs

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- Parent proof provides solid foundation
- The second Morley triangle is well-documented in literature
- Mainly extends existing computational approach

**Estimated Effort**:
- Exploration: 2-4 hours
- If tractable: 3-5 days

## References

### Papers
- Morley, F. (1899), "Extensions of Clifford's chain theorem"
- Oakley, C.O. and Baker, J.C. (1978), "The Morley trisector theorem"
- Conway, J.H. (2005), "The Power of Mathematics" — elementary proof

### Mathlib
- `Mathlib.Geometry.Euclidean` — Euclidean geometry
- `Mathlib.Analysis.SpecialFunctions.Trigonometric` — trig functions

## Metadata

```yaml
tags:
  - geometry
  - triangle
  - trisector
  - equilateral
  - wiedijk-100
related_proofs:
  - morleys-theorem
  - feuerbachs-theorem
difficulty: medium-high
source: gallery-gap
created: 2026-03-30
```
