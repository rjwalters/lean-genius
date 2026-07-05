# Problem: n-Point Telescoping Reverse Triangle Inequality

**Slug**: triangle-inequality-oq-06-oq-02
**Created**: 2026-07-05T01:43:16-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

In any metric space $(X, d)$, for points $x_0, x_1, \dots, x_n$ and an
arbitrary base point $y$,

$$
\bigl|\, d(x_0, x_n) - d(y, x_n) \,\bigr| \;\le\; d(x_0, y) + \sum_{i=0}^{n-1} d(x_i, x_{i+1}),
$$

and more sharply the telescoping form

$$
\Bigl|\, d(x_0, x_n) - d(y, x_n) \,\Bigr| \;\le\; d(x_0, y),
\qquad
d(x_0, x_n) \le \sum_{i=0}^{n-1} d(x_i, x_{i+1}),
$$

with the **attainment condition**: equality in the polygonal bound
$d(x_0, x_n) = \sum_{i=0}^{n-1} d(x_i, x_{i+1})$ holds iff every
intermediate $x_i$ lies "between" $x_0$ and $x_n$ (each partial
$x_i$ is on a geodesic / metric segment, i.e. $d(x_0,x_i)+d(x_i,x_n)=d(x_0,x_n)$).

### Plain Language

The ordinary reverse triangle inequality says $|d(x,z) - d(y,z)| \le d(x,y)$.
This problem asks for the *n-point telescoping refinement*: chain the reverse
inequality along a polygonal path $x_0 \to x_1 \to \cdots \to x_n$ so the total
"detour" is controlled by the sum of consecutive leg lengths, and pin down
exactly when the chain is tight (all intermediate points collinear/between on
a geodesic).

### Why This Matters

The reverse triangle inequality and its polygonal/telescoping form are the
backbone of rectifiable-curve length, geodesic betweenness, and completeness
arguments (Hopf–Rinow). Making the n-point form and its attainment condition
explicit in Lean packages a reusable lemma that downstream metric-geometry
formalizations (arc length, geodesic segments) can call directly.

## Known Results

### What's Already Proven

- `dist_triangle`, `dist_triangle4`, and the reverse form `abs_dist_sub_le`
  in Mathlib's `Mathlib.Topology.MetricSpace.Basic`.
- The base gallery proof **triangle-inequality** (status: verified, badge:
  mathlib, 0 axioms) establishing the core inequality and Minkowski form.

### What's Still Open

- The uniform n-point telescoping statement with an explicit `Finset.range`
  sum over the polygonal legs.
- The attainment/equality characterization in terms of metric betweenness.

### Our Goal

Prove the telescoping bound $d(x_0,x_n) \le \sum_{i<n} d(x_i,x_{i+1})$ by
induction over `n` (Mathlib's `dist_le_range_sum` / `dist_le_Ico_sum_dist`
may already supply it or a close variant), then derive the reverse
n-point corollary and state the betweenness attainment condition.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| triangle-inequality | Direct parent; supplies core `dist_triangle` and reverse form | metric inequalities |
| spherical-law-of-cosines | Metric/geometry sibling using distance bounds | trigonometric distance |

## Initial Thoughts

### Potential Approaches

1. **Induction on the polygonal length** (Approach A)
   - Base: `n = 0` trivial; step: `dist_triangle` on $x_0, x_{n}, x_{n+1}$.
   - Why it might work: Mathlib very likely already has
     `dist_le_Ico_sum_dist` or `dist_le_range_sum_dist`; reuse directly.
   - Risk: exact lemma name/shape mismatch; may need a thin wrapper.

2. **Attainment via `Metric` betweenness** (Approach B)
   - Characterize equality using `Wbtw`/`Sbtw` or the metric-segment
     predicate `d(x_0,x_i) + d(x_i,x_n) = d(x_0,x_n)`.
   - Risk: betweenness in a *general* metric space (no linear structure)
     needs the additive-distance definition, not the affine `Wbtw`.

### Key Difficulties

- Stating betweenness in a bare metric space (no vector-space structure).
- Aligning index conventions (`Finset.range n` vs `Ico`) with Mathlib.

### What Would a Proof Need?

- Key lemma 1: telescoping polygonal bound (likely `dist_le_range_sum_dist`).
- Key lemma 2: reverse form combining the above with `abs_dist_sub_le`.
- Attainment: an iff between chain-equality and pairwise metric betweenness.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The core telescoping inequality is a standard induction and probably
  already in Mathlib (`dist_le_Ico_sum_dist`).
- The novel content is the reverse n-point corollary plus a clean statement
  of the attainment condition.
- Parent proof is fully verified, so all supporting infrastructure exists.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days
- If hard (attainment subtleties): up to a week

## References

### Mathlib
- `Mathlib.Topology.MetricSpace.Basic` — `dist_triangle`, `abs_dist_sub_le`.
- `Mathlib.Topology.MetricSpace.*` — `dist_le_Ico_sum_dist` / range-sum forms.

## Metadata

```yaml
tags:
  - analysis
  - metric-geometry
  - triangle-inequality
related_proofs:
  - triangle-inequality
  - spherical-law-of-cosines
difficulty: medium
source: gallery-gap
created: 2026-07-05T01:43:16-07:00
```

**Significance**: 5/10
**Tractability**: 6/10
