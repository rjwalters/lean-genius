# Problem: Menelaus's theorem: collinearity via signed side ratios

## Statement

### Plain Language
AVAILABLE: Formalize Menelaus's theorem in the affine/Euclidean plane: for triangle ABC and points X on line BC, Y on line CA, Z on line AB, the three points are collinear iff the product of signed ratios (BX/XC)*(CY/YA)*(AZ/ZB) = -1. Recommended route: work in EuclideanSpace R (Fin 2) or a real affine space; encode each division point via an affine combination X = B + t*(C-B), express collinearity through a 2x2 determinant (or AffineMap), and reduce the equivalence to a polynomial identity dischargeable by field_simp + ring. Complements the existing Ceva gallery entries (Ceva = concurrency of cevians; Menelaus = collinearity of a transversal). Not a named Mathlib result.

### Formal Statement
$$
\text{(formal statement to be added)}
$$

## Classification

```yaml
tier: B
significance: 7
tractability: 6
tags:
  - seeker-selected
  - euclidean-geometry
  - affine-geometry
  - collinearity
  - triangle-geometry
  - research
```

**Significance**: 7/10
**Tractability**: 6/10

## Why This Matters

1. **Research value** - Formalize Menelaus's theorem in the affine/Euclidean plane: for triangle ABC and points X on line BC, Y on line CA, Z on line AB, the three points are collinear iff the product of signed ratios (BX/XC)*(CY/YA)*(AZ/ZB) = -1. Recommended route: work in EuclideanSpace R (Fin 2) or a real affine space; encode each division point via an affine combination X = B + t*(C-B), express collinearity through a 2x2 determinant (or AffineMap), and reduce the equivalence to a polynomial identity dischargeable by field_simp + ring. Complements the existing Ceva gallery entries (Ceva = concurrency of cevians; Menelaus = collinearity of a transversal). Not a named Mathlib result.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| --- | --- |
