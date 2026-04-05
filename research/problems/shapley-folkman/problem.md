# Problem: Shapley-Folkman Lemma — Complete the Lean Formalization

**Slug**: shapley-folkman
**Created**: 2026-04-05T13:14:12-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For sets } S_i \subseteq \mathbb{R}^d, \text{ any } x \in \operatorname{conv}\!\left(\sum_{i \in I} S_i\right)
\text{ has a decomposition with at most } d \text{ summands in } \operatorname{conv}(S_i) \setminus S_i.
$$

### Plain Language

A point in the convex hull of a Minkowski sum can always be expressed as a sum where
almost all summands come from the original (non-convexified) sets. Only $d$ summands
need to come from convex hulls rather than the original sets, regardless of how many
sets are summed.

### Why This Matters

The Shapley-Folkman lemma underpins existence of approximate equilibria in large economies
with non-convex preferences (Arrow-Debreu theory), nearly-convex optimization, and
combinatorial geometry. The gallery formalization (Proofs/ShapleyFolkman.lean) has the main
theorem proved but 3 sorries remain: `reduce_excess_by_one` (core step), `sum_close_to_convexHull`
(corollary), and `repeated_sum_nearly_convex` (corollary).

## Known Results

### What's Already Proven

- `convexHull_not_mem_requires_two`, `excess_vertices_affine_dependent`, `linearDependent_coefficients`
- `exists_decomposition` — initial decomposition from convHull membership
- `shapley_folkman` (main theorem) — proved by induction using `reduce_excess_by_one` as sorry

### What's Still Open

1. **`reduce_excess_by_one`** (line 241): affine dependence → remove one excess index (Carathéodory-style)
2. **`sum_close_to_convexHull`** (line 304): corollary from `x ∈ convexHull ℝ (∑ Sᵢ)`
3. **`repeated_sum_nearly_convex`** (line 316): n-fold Minkowski sum corollary

### Our Goal

Fill all 3 sorries in `Proofs/ShapleyFolkman.lean`. Corollaries #2 and #3 should follow
from the main theorem. `reduce_excess_by_one` is the hard core step.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `shapley-folkman` | The formalization itself | Convex analysis, finrank, affine independence |

## Initial Thoughts

### Potential Approaches

1. **Aristotle first on corollaries**: `sum_close_to_convexHull` and `repeated_sum_nearly_convex`
   may be auto-provable since they follow from `shapley_folkman` + membership rewrites.

2. **Manual `reduce_excess_by_one`**: find λ s.t. ∑ λᵢ = 0, ∑ λᵢfᵢ = 0 with some λᵢ ≠ 0
   (from `linearDependent_coefficients`). Perturb f by t·λ until one component hits ∂Sᵢ.

3. **Mathlib Carathéodory**: check if `Convex.caratheodory` or similar can close `reduce_excess_by_one`.

### Key Difficulties

- `reduce_excess_by_one` needs explicit construction of the perturbed decomposition
- Must show perturbed point stays in convHull(Sᵢ) throughout

### What Would a Proof Need?

- `AffineIndependent` and affine dependence theory from Mathlib
- `Module.finrank` bounds and FiniteDimensional infrastructure
- Linear algebra: finding t∗ where perturbed component hits boundary

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Two corollaries are likely low-effort (structural follows from main theorem)
- Core step requires careful algebra but the mathematical structure is clear
- Mathlib has all prerequisites (FiniteDimensional, convexHull, AffineIndependent)
- Aristotle is an explicit goal per the gallery openQuestions

## References

### Papers
- Shapley & Shubik (1966) — "Quasi-cores in a monetary economy with nonconvex preferences"
- Starr (1969) — "Quasi-equilibria in markets with non-convex preferences"

### Mathlib
- `Mathlib.Analysis.Convex.Hull` — convexHull and basic properties
- `Mathlib.LinearAlgebra.AffineSpace.Independent` — AffineIndependent
- `Mathlib.LinearAlgebra.FiniteDimensional` — Module.finrank

## Metadata

```yaml
tags:
  - convex-analysis
  - economics
  - formalization
  - aristotle-candidate
  - mathlib-target
related_proofs:
  - shapley-folkman
difficulty: medium
source: gallery-gap
created: 2026-04-05T13:14:12-07:00
```
