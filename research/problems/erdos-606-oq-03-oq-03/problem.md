# Problem: Formalize Sylvester-Gallai Theorem in Lean

**Slug**: erdos-606-oq-03-oq-03
**Created**: 2026-04-05T06:26:11-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

**Sylvester-Gallai Theorem**: Given $n \geq 3$ non-collinear points in $\mathbb{R}^2$, there exists a line passing through exactly 2 of the points (an "ordinary line").

In Lean 4:
```lean
theorem sylvester_gallai (S : Finset (ℝ × ℝ)) (hn : 3 ≤ S.card)
    (hncol : ¬ Collinear ℝ (S : Set (ℝ × ℝ))) :
    ∃ p q ∈ S, p ≠ q ∧ ∀ r ∈ S, r ≠ p → r ≠ q →
      ¬ Collinear ℝ ({p, q, r} : Set (ℝ × ℝ)) := sorry
```

### Plain Language

Given any finite set of points in the plane (at least 3, not all on one line), you can always find a line that passes through exactly 2 of the points.

### Why This Matters

- Sylvester-Gallai is a foundational result in combinatorial geometry
- The parent proof (`erdos-606-oq-03`, Hyperplane Determination in Higher Dimensions) currently lacks this formalization
- Kelly's 1948 proof is elementary and a natural candidate for Lean formalization
- No complete Lean formalization of this theorem appears in Mathlib

## Known Results

### What's Already Proven

- Mathlib has `Collinear` predicate for `ℝ`-vector spaces
- Mathlib has `EuclideanGeometry` and metric space infrastructure
- Kelly's proof reduces to: among all (point, line) pairs where point is off the line, find the pair minimizing distance; then show the foot of perpendicular is an ordinary line

### Kelly's Proof Sketch

1. Among all pairs (p, L) where p ∈ S, L is a line through ≥ 2 points of S, p ∉ L — pick the pair minimizing dist(p, L)
2. The line L, going through points a, b (∈ S), has at most 1 point of S between the foot F of the perpendicular from p to L and either a or b
3. If ≥ 2 points of S are on the same side of F on L, swapping gives a closer (point, line) pair — contradiction
4. Therefore L contains exactly 2 points of S

### Our Goal

Formalize the Sylvester-Gallai theorem in Lean 4, preferably using Kelly's elementary metric proof.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| erdos-606-oq-03 | Parent: Hyperplane Determination |
| erdos-606 | Grandparent: Sylvester-Gallai directions |

## Initial Thoughts

### Potential Approaches

1. **Kelly's metric proof** (most tractable):
   - Formalize dist(p, L) for points and lines in ℝ²
   - Use `Finset.exists_min_image` for the minimum distance pair
   - Case analysis using `Mathlib.Analysis.InnerProductSpace.PiL2`
   - Risk: Distance from point to line API in Mathlib may be thin

2. **Projective geometry approach**:
   - Use projective duality: ordinary lines ↔ interior points of convex hull
   - Mathlib has some projective geometry but likely insufficient
   - Risk: More infrastructure required

3. **Contradiction approach via collinearity**:
   - Assume all lines pass through ≥ 3 points
   - Derive contradiction using finite intersection counting
   - Risk: Hard to formalize the counting argument cleanly

### Key Mathlib Lemmas to Find

- `EuclideanGeometry.dist_sq_smul_dist_left` or distance to line
- `Finset.exists_min_image` — for finding minimum distance pair
- `Collinear` API — `collinear_iff_exists_forall_eq_smul_vadd`
- Inner product space projection lemmas

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Kelly's proof is elementary in mathematics, but requires real analysis in Lean
- Mathlib has the building blocks (Euclidean geometry, metric spaces, Finset)
- Main challenge: distance from point to line in ℝ²
- Alternative: find a purely combinatorial formulation that avoids metric arguments

**Estimated Effort**: 1-2 weeks

## Metadata

```yaml
tags:
  - geometry
  - incidence-geometry
  - combinatorics
  - lean-mathlib
  - collinearity
related_proofs:
  - erdos-606-oq-03
  - erdos-606
difficulty: medium
source: gallery-gap
created: 2026-04-05T06:26:11-07:00
```
