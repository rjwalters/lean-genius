# Problem: British Flag theorem: PA² + PC² = PB² + PD² for any point and rectangle

## Statement

### Plain Language
AVAILABLE: Formalize the British Flag theorem in the Euclidean plane: for a rectangle ABCD and any point P, the sums of squared distances to opposite corners are equal, dist P A ^ 2 + dist P C ^ 2 = dist P B ^ 2 + dist P D ^ 2. Recommended route: work in EuclideanSpace R (Fin 2); place the rectangle at A=(0,0), B=(w,0), C=(w,h), D=(0,h) and P=(x,y), expand each squared distance via EuclideanSpace.dist_eq over Fin 2, and discharge the resulting polynomial identity with ring. A coordinate-free variant states it for any point relative to a rectangle and follows from the parallelogram law. Not a named Mathlib result; a clean coordinate-algebra companion to the Pythagoras gallery family.

### Formal Statement
$$
\operatorname{dist}(P,A)^2 + \operatorname{dist}(P,C)^2 = \operatorname{dist}(P,B)^2 + \operatorname{dist}(P,D)^2
$$

## Classification

```yaml
tier: B
significance: 6
tractability: 8
tags:
  - seeker-selected
  - euclidean-geometry
  - coordinate-geometry
  - metric-geometry
  - research
```

**Significance**: 6/10
**Tractability**: 8/10

## Why This Matters

1. **Research value** - Formalize the British Flag theorem: for a rectangle ABCD and any point P, dist P A ^ 2 + dist P C ^ 2 = dist P B ^ 2 + dist P D ^ 2. A direct coordinate-algebra proof (place rectangle on axes, expand squared distances over Fin 2, finish with ring) that extends the Pythagoras gallery family and is absent from Mathlib.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| --- | --- |
