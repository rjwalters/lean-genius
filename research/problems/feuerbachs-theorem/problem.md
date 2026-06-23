# Problem: Prove Feuerbach Distance Relations via Coordinate Computation

**Slug**: feuerbachs-theorem-oq-01
**Created**: 2026-03-11
**Status**: Active
**Source**: gallery-extension

## Problem Statement

### Formal Statement

For a triangle with circumradius R, inradius r, nine-point center N, and incenter I:

d(N, I) = |R/2 - r|

This is Feuerbach's tangency condition: the nine-point circle (radius R/2) is internally tangent to the incircle (radius r).

Similarly, for each excircle center I_k with radius r_k:
d(N, I_k) = R/2 + r_k

### Plain Language

The existing Lean formalization of Feuerbach's theorem axiomatizes the key distance relations. Can we replace these axioms with actual proofs using coordinate computation?

### Why This Matters

Feuerbach's theorem (Wiedijk #29) is currently axiom-based. Completing the coordinate proofs would upgrade it to fully verified — significant for the Wiedijk 100 collection.

## Known Results

### What's Already Proven

- Triangle framework with special points — `proofs/Proofs/FeuerbachsTheorem.lean`
- Euler line relation G = (O + 2H)/3 — proved by direct computation
- Nine-point center N = (O + H)/2 — proved
- 3-4-5 right triangle verification — computed
- Euler's identity OI^2 = R^2 - 2Rr is the key bridge

### What's Still Open

- Core distance relations d(N,I) = |R/2 - r| — currently axiomatized
- Excircle tangency d(N, I_k) = R/2 + r_k — currently axiomatized

### Our Goal

Replace the axiomatized distance relations with proofs, upgrading Feuerbach's theorem from axiom-based to fully verified.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| feuerbachs-theorem | Direct source — axioms to replace | Coordinate geometry, triangle centers |
| cevas-theorem | Triangle geometry | Barycentric coordinates |
| law-of-cosines | Triangle computation | Distance formulas |

## Initial Thoughts

### Potential Approaches

1. **Direct coordinate computation**: Place triangle at convenient coordinates, compute all distances algebraically
2. **Via Euler's identity**: Prove OI^2 = R^2 - 2Rr first, then derive NI = |R/2 - r|

### Key Difficulties

- Very long algebraic expressions involving side lengths a, b, c
- Need to handle the absolute value in |R/2 - r|
- `ring` tactic may struggle with expression size

## Tractability Assessment

**Difficulty**: Challenging

**Justification**:
- The proof strategy is well-known (coordinate computation)
- The file already has the coordinate framework set up
- Main challenge is managing algebraic complexity in Lean

## Metadata

```yaml
tags:
  - geometry
  - triangle
  - circle
  - wiedijk-100
related_proofs:
  - feuerbachs-theorem
difficulty: challenging
source: gallery-extension
created: 2026-03-11
```
