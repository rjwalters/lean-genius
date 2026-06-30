# Problem: Routh's theorem: inner-triangle area ratio from cevian ratios

## Statement

### Plain Language
AVAILABLE: Formalize Routh's theorem: if cevians divide the sides of triangle ABC in ratios BX:XC = x:1, CY:YA = y:1, AZ:ZB = z:1, then the inner triangle formed by the three cevians has area ratio (x*y*z - 1)^2 / ((x*y + y + 1)(y*z + z + 1)(z*x + x + 1)) to triangle ABC. Recommended route: place A,B,C in affine/barycentric coordinates, compute the three pairwise cevian intersections by solving linear systems, and obtain the area ratio from the 3x3 determinant of the inner vertices; the closing identity is dischargeable by field_simp + ring. Sanity checks: area -> 0 when xyz = 1 (Ceva concurrency), and the one-seventh-area medial case x=y=z=2. Not a named Mathlib result.

### Formal Statement
$$
\text{(formal statement to be added)}
$$

## Classification

```yaml
tier: B
significance: 6
tractability: 5
tags:
  - seeker-selected
  - euclidean-geometry
  - affine-geometry
  - area-ratio
  - triangle-geometry
  - research
```

**Significance**: 6/10
**Tractability**: 5/10

## Why This Matters

1. **Research value** - Formalize Routh's theorem: if cevians divide the sides of triangle ABC in ratios BX:XC = x:1, CY:YA = y:1, AZ:ZB = z:1, then the inner triangle formed by the three cevians has area ratio (x*y*z - 1)^2 / ((x*y + y + 1)(y*z + z + 1)(z*x + x + 1)) to triangle ABC. Recommended route: place A,B,C in affine/barycentric coordinates, compute the three pairwise cevian intersections by solving linear systems, and obtain the area ratio from the 3x3 determinant of the inner vertices; the closing identity is dischargeable by field_simp + ring. Sanity checks: area -> 0 when xyz = 1 (Ceva concurrency), and the one-seventh-area medial case x=y=z=2. Not a named Mathlib result.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| --- | --- |
