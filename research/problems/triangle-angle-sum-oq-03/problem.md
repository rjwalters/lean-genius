# Problem: Triangle Angle Sum: Mathlib Angle Function Degenerate Cases

**Slug**: triangle-angle-sum-oq-03
**Created**: 2026-04-22
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For collinear points } A, B, C \in \mathbb{R}^2, \text{ what does } \angle BAC + \angle ABC + \angle BCA \text{ evaluate to in Lean/Mathlib?}
$$

Specifically: When `(A, B, C)` are collinear, what values does `EuclideanGeometry.angle A B C` return, and does the standard triangle angle sum theorem extend gracefully to this degenerate case?

In Lean 4 (Mathlib):
```lean
-- What does this evaluate to when A, B, C are collinear?
example (A B C : EuclideanSpace ℝ (Fin 2)) (h : Collinear ℝ {A, B, C}) :
    EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A + EuclideanGeometry.angle C A B = π ∨
    EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A + EuclideanGeometry.angle C A B = 0 := by
  sorry
```

### Plain Language

The triangle angle sum theorem states that for a non-degenerate triangle, the interior angles sum to π radians. But what happens when the three points are collinear (forming a "degenerate triangle")?

In Mathlib, `EuclideanGeometry.angle A B C` (or `Real.angle`) uses a specific definition based on the inner product. For collinear points:
- If B lies between A and C: the angle at B is π, while angles at A and C are 0, so sum = π
- If A lies between B and C: the angle at A is π, while angles at B and C are 0
- For all cases, is the sum still π or 0?

The question is both about the mathematical content AND about how Lean/Mathlib's implementation handles these cases.

### Why This Matters

Understanding how Mathlib handles degenerate geometric configurations is important for:
1. Writing robust formal proofs that don't silently break at boundaries
2. Proving the angle sum theorem in full generality
3. Understanding the `Real.angle` and `EuclideanGeometry.angle` APIs
4. Informing how future Lean formalizations handle boundary cases

This is an exploratory investigation that directly supports robust use of Mathlib's geometry library.

## Known Results

### What's Already Proven

- Triangle angle sum (non-degenerate): `EuclideanGeometry.angle_add_angle_add_angle_eq_pi` — for non-collinear points
- `Real.angle` is defined via `Real.arccos (inner_product / ...)`, returning values in `[0, π]`
- For any two vectors, `Real.angle v w = 0` iff `∃ r > 0, w = r • v` (same direction)
- For any two vectors, `Real.angle v w = π` iff `∃ r < 0, w = r • v` (opposite direction)

### What's Still Open

- What does `EuclideanGeometry.angle A B C` return when A = B or B = C (coincident points)?
- Does `angle_add_angle_add_angle_eq_pi` hold vacuously for collinear points or fail?
- Is there a unified theorem covering both degenerate and non-degenerate cases?

### Our Goal

1. Identify the relevant Mathlib lemmas for `EuclideanGeometry.angle` degenerate cases
2. Determine what value the angle sum takes for collinear configurations
3. Prove a statement about the angle sum for degenerate triangles (or show the existing theorem's hypotheses exclude them)

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `triangle-angle-sum` | Parent proof — the non-degenerate case | `EuclideanGeometry.angle`, inner products |
| `feuerbachs-theorem-defs` | Uses geometric API in Lean | Affine geometry, Mathlib |

## Initial Thoughts

### Potential Approaches

1. **Compute directly in Lean**: Use `#eval` or `native_decide` to compute `EuclideanGeometry.angle` for specific collinear examples and observe the output.
   - Why it might work: Fast empirical check before formal proof
   - Risk: Might not generalize

2. **Trace through Mathlib definition**: Follow `EuclideanGeometry.angle` → `Real.angle` → `Real.arccos` for the collinear case.
   - Why it might work: Direct definitional unfolding
   - Risk: May require inner product computation

3. **Search Mathlib for degenerate case lemmas**: Look for `angle_eq_zero`, `angle_eq_pi`, `Collinear` + `angle` combinations.
   - Why it might work: Mathlib may already have these as lemmas
   - Risk: May need to combine multiple results

### Key Difficulties

- Mathlib's `EuclideanGeometry.angle` requires care with degenerate inputs (zero vectors)
- `Real.arccos` of values outside `[-1, 1]` needs careful handling
- The "degenerate triangle" has no unique canonical form

### What Would a Proof Need?

- `Collinear ℝ {A, B, C}` unfolded in terms of inner products/coordinates
- Lemma: if A, B, C collinear with B between A and C, then `angle A B C = π`
- Lemma: if A, B, C collinear with A between B and C, then `angle B A C = π`  
- Conclusion: angle sum is still π (just differently distributed)

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- The mathematical content is clear: for collinear points, one angle is π and the rest are 0
- Mathlib has all the necessary lemmas about `Real.angle` and collinearity
- This is exploratory (OBSERVE phase focuses on finding the right lemmas)
- `EuclideanGeometry.angle_add_angle_add_angle_eq_pi` may already handle this

**Estimated Effort**:
- Exploration: 2-4 hours (find relevant Mathlib lemmas)
- If tractable: 1-2 days (write and verify the formal proof)
- If hard: 3-5 days (if degenerate case requires bespoke reasoning)

## References

### Mathlib
- `Mathlib.Geometry.Euclidean.Angle.Sphere` — main angle theory
- `EuclideanGeometry.angle_add_angle_add_angle_eq_pi` — non-degenerate case
- `Real.angle` — the underlying real angle definition
- `Mathlib.Analysis.InnerProductSpace.Basic` — inner product geometry

## Metadata

```yaml
tags:
  - geometry
  - lean-mathlib
  - euclidean-geometry
  - degenerate-cases
  - angle-theory
related_proofs:
  - triangle-angle-sum
  - feuerbachs-theorem-defs
difficulty: low
source: gallery-gap
created: 2026-04-22
```

**Significance**: 6/10
**Tractability**: 7/10
