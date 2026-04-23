# Problem: Pascal's Hexagon: Brianchon Dual via Projective Duality Formalization

**Slug**: pascals-hexagon-oq-02
**Created**: 2026-04-23T13:50:28+02:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

**Brianchon's Theorem** (dual of Pascal's): If a hexagon is circumscribed about a conic
section (each side is tangent to the conic), then the three main diagonals (connecting
opposite vertices) are concurrent.

Formally, given a hexagon $ABCDEF$ with each side tangent to a conic $C$, the diagonals
$AD$, $BE$, $CF$ meet at a single point (the Brianchon point).

### Plain Language

Pascal's hexagon theorem states: if six points lie on a conic, the three intersection
points of opposite sides are collinear (forming the "Pascal line"). By projective duality,
Brianchon's theorem is the exact dual: six tangent lines to a conic form a hexagon
whose three main diagonals are concurrent.

The question is: can **Brianchon's theorem** be formally proved from **Pascal's theorem**
via **projective duality** in Lean 4?

This would require:
1. A formalization of projective duality (points ↔ lines in projective space)
2. Applying duality to Pascal's theorem to obtain Brianchon's theorem
3. Handling the conic duality (point conic ↔ line conic)

### Why This Matters

- **Projective duality** is a fundamental principle in algebraic geometry
- A formal duality-based proof would validate that Lean 4 can reason about dual spaces
- Connects the `pascals-hexagon` gallery entry to broader projective geometry formalization
- Brianchon (1806) discovered this theorem by applying duality to Pascal's 1639 result

## Known Results

### What's Already Proven

- `pascals-hexagon` (gallery) — Pascal's theorem formalized in Lean 4
- Mathlib has projective geometry in `Mathlib.Geometry.Projective`
- Mathlib: `ProjectivePlane`, `DualProjectivePlane` types may exist

### What's Still Open

- Formal projective duality as a Lean 4 equivalence
- Brianchon's theorem statement in the Mathlib projective framework
- Connection between line conic (dual conic) and point conic

### Our Goal

Prove Brianchon's theorem from Pascal's theorem via formal projective duality:
1. Identify the dual statement of Pascal's theorem
2. Verify duality maps collinearity to concurrence correctly
3. State and prove Brianchon's theorem as a consequence

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| pascals-hexagon | Parent proof — Pascal's theorem | Projective geometry, cross-ratio |
| feuerbachs-theorem-defs-oq-04 | Mathlib affine/projective geometry | Affine framework |
| ptolemys-theorem-oq-01-oq-01 | Classical geometry formalization | Circle geometry |

## Initial Thoughts

### Potential Approaches

1. **Direct duality map**: Define projective duality as a map `ProjPlane → DualProjPlane`
   that swaps points/lines, then apply it to the Pascal's theorem proof.
   - Why it might work: Clean categorical approach; duality is an involution
   - Risk: Mathlib's projective plane formalization may not have a ready dual plane

2. **Coordinate-based proof**: Use homogeneous coordinates; duality swaps
   `[a:b:c]` (point) with `ax + by + cz = 0` (line). Verify algebraically that
   Pascal's cross-ratio argument dualizes to Brianchon's concurrence.
   - Why it might work: More computational, avoids abstract duality framework
   - Risk: Heavier algebra, less elegant

3. **Direct proof** (without duality): Prove Brianchon's theorem independently
   using the dual Cayley-Bacharach or direct conic arguments.
   - Why it might work: May be more tractable in Lean 4
   - Risk: Doesn't demonstrate projective duality formally

### Key Difficulties

- Lean 4's projective plane API may not have explicit duality between point/line conics
- The notion of "tangent to a conic" requires differentiability or algebraic tangency
- Concurrence (three lines meeting at one point) needs careful handling at infinity

### What Would a Proof Need?

- Key lemma 1: Projective duality maps Pascal's collinearity to Brianchon's concurrence
- Key lemma 2: Dual of a point conic is a line conic
- Key lemma 3: The Pascal hexagon dualizes to the Brianchon hexagon
- Technical: `Mathlib.Geometry.Projective` API compatibility

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is classical and well-understood
- The main challenge is Mathlib API coverage for projective duality
- Alternative: coordinate-based proof avoids abstract duality framework
- Related: `pascals-hexagon` proof exists as a template

**Estimated Effort**:
- Exploration: 2 days (survey Mathlib projective geometry API)
- If tractable (via duality): 1-2 weeks
- Fallback (direct proof): 1 week (less elegant but more feasible)

## References

### Papers
- Brianchon, C. J. (1806) — "Mémoire sur les surfaces courbes du second degré"
- Pascal, B. (1639) — "Essai pour les coniques" (original hexagram result)

### Mathlib
- `Mathlib.Geometry.Projective` — projective plane structures
- `Mathlib.LinearAlgebra.ProjectiveSpace` — projective space foundations

## Metadata

```yaml
tags:
  - geometry
  - projective
  - conic
  - collinearity
  - wiedijk-100
  - classic
  - duality
related_proofs:
  - pascals-hexagon
  - feuerbachs-theorem-defs-oq-04
  - ptolemys-theorem-oq-01-oq-01
difficulty: medium
source: gallery-gap
created: 2026-04-23T13:50:28+02:00
```
