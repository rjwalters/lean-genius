# Erdős Problem #353: Geometric Configurations in Sets of Infinite Measure

**Lean file**: `proofs/Proofs/Erdos353Problem.lean`
**Sorries**: 1
**Status**: available
**Tier**: B | **Significance**: 6/10 | **Tractability**: 5/10

## Problem Statement

Erdős #353: If A ⊆ ℝ² has positive measure, must A contain the vertices of an isosceles triangle of every area t > 0?

## The Sorry

```lean
theorem scaling_property (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : HasInfiniteMeasure A) (t : ℝ) (ht : t > 0) :
    HasIsoscelesTriangleWithArea A t := by
  sorry -- Follows from scaling argument
```

**Idea**: The scaling argument: if A has positive measure, it contains isosceles triangles of some area t₀. Scaling A by factor √(t/t₀) gives triangles of area t. But this requires scaling A, not triangles within A.

## Mathematical Content

This likely uses a density/measure argument:
1. By Lebesgue density theorem, A has density points
2. Near a density point, A looks like a full ball
3. In a ball, we can find isosceles triangles of any area up to some bound
4. Scaling: if the result holds for t₀, use a homothety

## Challenge

The `HasInfiniteMeasure` assumption (vs positive measure) may be key. With infinite measure, translation of triangles is possible.

## Approach

1. Read the full `Erdos353Problem.lean` to understand `HasIsoscelesTriangleWithArea`
2. Check what's already proved in the file
3. The scaling property: if we have area t₀ triangle, scale all coordinates by √(t/t₀) to get area t
4. But we need the scaled version to be WITHIN A (or find it directly)
5. Consider: infinite measure → A is dense enough everywhere?

## Related Gallery Proof

- `src/data/proofs/erdos-353/` — Erdős Problem #353
- `proofs/Proofs/Erdos353Problem.lean` — file with sorry

## First Steps (OBSERVE phase)

1. Read `Erdos353Problem.lean` fully
2. What lemmas are already proved? Is there a base case proved?
3. What exactly is `HasInfiniteMeasure`?
4. Can we find a direct density argument using `MeasureTheory.Measure.measure_inter_pos`?
