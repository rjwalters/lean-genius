# Problem: Varignon's theorem: side midpoints of any quadrilateral form a parallelogram

## Statement

### Plain Language
AVAILABLE: Formalize Varignon's theorem: for any quadrilateral with vertices A, B, C, D (modeled over ℂ or EuclideanSpace R (Fin 2)), the midpoints of the four sides form a parallelogram. Recommended route: over ℂ set the midpoints mAB=(A+B)/2, mBC=(B+C)/2, mCD=(C+D)/2, mDA=(D+A)/2 and prove the parallelogram condition mAB - mBC = mDA - mCD (equivalently mAB + mCD = mBC + mDA), each side reducing to (A-C)/2; finish with ring. Holds for arbitrary (even non-convex or skew) quadrilaterals since the proof is purely algebraic. Not a named Mathlib result; complements the van Aubel and Napoleon complex-number gallery entries.

### Formal Statement
$$
\frac{A+B}{2} - \frac{B+C}{2} = \frac{D+A}{2} - \frac{C+D}{2}
$$

## Classification

```yaml
tier: B
significance: 6
tractability: 8
tags:
  - seeker-selected
  - euclidean-geometry
  - complex-numbers
  - quadrilateral
  - research
```

**Significance**: 6/10
**Tractability**: 8/10

## Why This Matters

1. **Research value** - Formalize Varignon's theorem: the midpoints of the sides of any quadrilateral form a parallelogram. A one-line complex-number identity (the parallelogram condition reduces to (A-C)/2 on both sides via ring), holding for arbitrary quadrilaterals, that extends the van Aubel / Napoleon complex-number gallery family and is absent from Mathlib.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| --- | --- |
