# Problem: Dual spherical law of cosines (angles version)

**Slug**: spherical-law-of-cosines-oq-03
**Created**: 2026-06-15T06:15:07.078468+00:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For a spherical triangle with angles } A,B,C \text{ and opposite sides } a,b,c:\quad \cos C = -\cos A \cos B + \sin A \sin B \cos c
$$

### Plain Language

The spherical law of cosines for sides relates the three side lengths a, b, c (arc lengths) and one angle C of a spherical triangle: cos c = cos a cos b + sin a sin b cos C. This task formalizes the DUAL law of cosines for angles, cos C = −cos A cos B + sin A sin B cos c, which expresses an angle in terms of the other two angles and the opposite side. Together the two laws give the complete side–angle duality of spherical trigonometry.

### Why This Matters

Completes the spherical law-of-cosines system and demonstrates the polar-triangle duality, a central structural fact of spherical geometry.

## Classification

```yaml
tier: C
significance: 5
tractability: 7
```

**Significance**: 5/10
**Tractability**: 7/10

## Known Results

### What's Already Proven

- Spherical law of cosines for sides: cos c = cos a cos b + sin a sin b cos C (gallery base result).

### What's Still Open

- The dual (angles) law of cosines as a Lean theorem.
- Deriving it cleanly via the polar/dual triangle from the sides law.

### Our Goal

Prove the dual law cos C = −cos A cos B + sin A sin B cos c, ideally via the polar triangle.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| spherical-law-of-cosines | Parent gallery proof this open question extends |

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Follows from the existing sides law by applying it to the polar triangle (A↔π−a, etc.).
- Trigonometric identities are well supported in Mathlib.
- Main work is setting up the polar-triangle correspondence rigorously.

## Metadata

```yaml
tags:
  - geometry
  - spherical-geometry
  - trigonometry
  - non-euclidean-geometry
  - challenging
  - connection
  - gallery-extracted
  - seeker-selected
  - research
related_proofs:
  - spherical-law-of-cosines
difficulty: medium
source: gallery-gap
created: 2026-06-15T06:15:07.078468+00:00
```
