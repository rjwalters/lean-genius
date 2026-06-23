# Problem: N-Dimensional Volume Formula V_n(r) = Int S_n(rho)

**Slug**: area-of-circle-oq-01-oq-02-oq-01
**Created**: 2026-03-06
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$V_n(r) = \int_0^r S_n(\rho)\, d\rho$$

where V_n(r) is the volume of the n-ball and S_n(rho) is the surface area of the (n-1)-sphere of radius rho.

### Plain Language

Can the relationship between n-dimensional volume and surface area be formalized for all n? This generalizes the 2D result A = integral of circumference.

### Why This Matters

This is a fundamental result in geometric measure theory connecting volumes and surface areas across dimensions.

## Known Results

### What's Already Proven

- `AreaOfCircle.lean` - 2D area via integration of circumference
- `AreaOfCircleOQ01OQ03.lean` - Related extensions
- Mathlib `MeasureTheory.measure_ball` for specific dimensions

### Our Goal

Formalize V_n(r) = integral of S_n(rho) for all n.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| area-of-circle | 2D base case | Integration, FTC |
| area-of-circle-oq-01-oq-02 | Volume-surface area connection | Dimensional analysis |

## Tractability Assessment

**Difficulty**: Medium

## Metadata

```yaml
tags:
  - analysis
  - geometry
  - measure-theory
  - integration
  - n-dimensional
related_proofs:
  - area-of-circle
  - area-of-circle-oq-01-oq-02
difficulty: medium
source: gallery-gap
created: 2026-03-06
```

**Significance**: 7/10
**Tractability**: 6/10
