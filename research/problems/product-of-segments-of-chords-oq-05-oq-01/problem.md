# Problem: External power of a point (secant–secant) for a sphere

**Slug**: product-of-segments-of-chords-oq-05-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

For a sphere with centre `O` and radius `r`, and a point `P` **outside** the sphere, any line
through `P` meeting the sphere at parameters `t₁, t₂` (signed along a unit direction) satisfies

$$
|t_1|\cdot|t_2| \;=\; \lVert P - O \rVert^2 - r^2 .
$$

### Plain Language

The parent entry (`product-of-segments-of-chords-oq-05`) establishes the interior "power of a
point" identity: for `P` inside the sphere, the product of the two chord segments is constant
(`r² − ‖P−O‖²`), independent of the line's direction. This child handles the **exterior**
branch: when `P` is outside, the unsigned product of the two secant distances equals the
positive power `‖P−O‖² − r²`. It mirrors the interior statement on the other side of the sphere.

### Why This Matters

Together the interior and exterior cases give the full, sign-aware "power of a point" theorem
in `n`-dimensional inner-product space — a clean, complete pair of named results rather than a
single half. The exterior case is what underlies the tangent–secant relation `tangent² = power`.

## Known Results

### What's Already Proven

- Parent `product-of-segments-of-chords-oq-05`: interior power-of-a-point identity
  `t₁·t₂ = r² − ‖P−O‖²` (signed product negative when `P` is inside).
- Vieta's formulas for the quadratic in `t` from `‖(P + t·d) − O‖² = r²`.
- Mathlib inner-product-space and `EuclideanSpace` API.

### What's Still Open

- The exterior statement with unsigned product `|t₁|·|t₂| = ‖P−O‖² − r²`.
- Confirming both roots have the *same sign* when `P` is outside (so `|t₁·t₂| = t₁·t₂`).

### Our Goal

Prove the exterior identity as a corollary of the same quadratic used by the parent: the
product of roots is `t₁·t₂ = ‖P−O‖² − r²` by Vieta, and outside the sphere this product is
positive, so `|t₁|·|t₂| = ‖P−O‖² − r²`. Package it mirroring OQ-01's interior statement.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| product-of-segments-of-chords-oq-05 | Direct parent; the interior branch | Vieta, inner product |
| product-of-segments-of-chords | Base chord-product (2D circle) result | intersecting chords |

## Initial Thoughts

### Potential Approaches

1. **Reuse the parent's quadratic**: the equation `‖(P + t·d) − O‖² = r²` expands to
   `t² + 2⟨P−O, d⟩ t + (‖P−O‖² − r²) = 0`; the constant term *is* the power. Product of
   roots is that constant term directly.
   - Why it might work: the algebra is already in the parent; only the sign analysis is new.
   - Risk: proving both roots share a sign (nonnegative constant term ⇒ same sign) cleanly.

2. **Discriminant + sign bookkeeping**: use that outside the sphere the constant term is
   positive and the discriminant is nonnegative to control root signs.
   - Why it might work: elementary quadratic reasoning.
   - Risk: `abs` manipulation over ordered fields.

### Key Difficulties

- Establishing `|t₁·t₂| = |t₁|·|t₂|` and that the product is nonnegative outside the sphere.
- Keeping the direction vector `d` a genuine unit vector so `t` is arc-length.

### What Would a Proof Need?

- Key lemma 1: Vieta product of roots equals `‖P−O‖² − r²` for the parametrized line.
- Key lemma 2: outside the sphere ⇒ constant term `> 0` ⇒ roots same sign ⇒ `|t₁|·|t₂|` form.
- Technical requirements: `inner_mul_le_norm_mul_norm`, real quadratic root/product lemmas.

## Tractability Assessment

**Difficulty**: Low-to-Medium

**Justification**:
- The parent already sets up and solves the parametrized quadratic.
- This is the mirror-image case; the incremental work is sign analysis and `abs`.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days

## References

### Mathlib
- `Mathlib.Analysis.InnerProductSpace.Basic` — inner product, norm-squared expansion.
- `Mathlib.Analysis.SpecialFunctions.Sphere` / `Mathlib.Geometry.Euclidean.Sphere` — sphere API.
- `Mathlib.Algebra.QuadraticDiscriminant` — root/product of a real quadratic.

## Metadata

```yaml
tags:
  - geometry
  - inner-product-space
  - power-of-a-point
  - vieta
related_proofs:
  - product-of-segments-of-chords-oq-05
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 6/10
