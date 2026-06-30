# Problem: Weitzenboeck's inequality: a^2+b^2+c^2 >= 4*sqrt(3)*Area

## Statement

### Plain Language
AVAILABLE: Formalize Weitzenboeck's inequality: for a triangle with side lengths a,b,c and area T, a^2 + b^2 + c^2 >= 4*sqrt(3)*T, with equality iff the triangle is equilateral. Recommended route: express the area via Heron's formula 16*T^2 = 2a^2b^2 + 2b^2c^2 + 2c^2a^2 - a^4 - b^4 - c^4, square the target to (a^2+b^2+c^2)^2 >= 48*T^2, and discharge the resulting SOS identity (a^2-b^2)^2 + (b^2-c^2)^2 + (c^2-a^2)^2 >= 0 with nlinarith/polyrith. Mathlib provides Real.sqrt and basic triangle/area lemmas. Not a named Mathlib result.

### Formal Statement
$$
\text{(formal statement to be added)}
$$

## Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - seeker-selected
  - euclidean-geometry
  - inequality
  - triangle-geometry
  - area
  - research
```

**Significance**: 6/10
**Tractability**: 7/10

## Why This Matters

1. **Research value** - Formalize Weitzenboeck's inequality: for a triangle with side lengths a,b,c and area T, a^2 + b^2 + c^2 >= 4*sqrt(3)*T, with equality iff the triangle is equilateral. Recommended route: express the area via Heron's formula 16*T^2 = 2a^2b^2 + 2b^2c^2 + 2c^2a^2 - a^4 - b^4 - c^4, square the target to (a^2+b^2+c^2)^2 >= 48*T^2, and discharge the resulting SOS identity (a^2-b^2)^2 + (b^2-c^2)^2 + (c^2-a^2)^2 >= 0 with nlinarith/polyrith. Mathlib provides Real.sqrt and basic triangle/area lemmas. Not a named Mathlib result.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| --- | --- |
