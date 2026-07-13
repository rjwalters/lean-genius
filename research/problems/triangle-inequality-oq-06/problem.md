# Problem: The Reverse Triangle Inequality Family and 1-Lipschitz Distance

**Slug**: triangle-inequality-oq-06
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: triangle-inequality

## Problem Statement

### Formal Statement

In a pseudometric space and a seminormed group:

$$
|\,d(x,z) - d(y,z)\,| \le d(x,y),\qquad
|\,d(x,y) - d(x',y')\,| \le d(x,x') + d(y,y'),\qquad
\big|\,\|a\| - \|b\|\,\big| \le \|a - b\|,
$$

and the distance function is `1`-Lipschitz in each argument.

### Plain Language

The parent `triangle-inequality` proves the forward inequality `d(x,z) ≤ d(x,y) + d(y,z)`.
This child collects its *reverse* companions into one coherent verified narrative: the
**reverse (second) triangle inequality** (distance changes by at most the step you take), its
**quadrilateral** strengthening (moving both endpoints), the **norm** version, and the
consequence that `d(x, ·)` is `1`-Lipschitz — hence continuous. Together these are the tools
that make metric geometry "stable under small perturbations."

### Why This Matters

The reverse inequalities are used constantly (continuity of the metric, well-definedness of
limits, stability estimates), but they are rarely presented as a unit. Mathlib has each piece
(`abs_dist_sub_le`, `dist_dist_dist_le`, `abs_norm_sub_norm_le`, `LipschitzWith.dist_right`),
so the value here is a curated, cross-referenced gallery entry that states the family, proves
the quadrilateral form as the headline, and derives continuity of the metric as a corollary.

## Known Results

### What's Already Proven

- Parent `triangle-inequality` is verified (0-axiom).
- Mathlib: `abs_dist_sub_le (x y z) : |dist x z - dist y z| ≤ dist x y`;
  `dist_dist_dist_le (x y x' y') : dist (dist x y) (dist x' y') ≤ dist x x' + dist y y'`;
  `abs_norm_sub_norm_le (a b) : |‖a‖ - ‖b‖| ≤ ‖a - b‖`;
  `norm_sub_norm_le`;
  `LipschitzWith.dist_right (x) : LipschitzWith 1 (dist x)`;
  `LipschitzWith.dist_left`.

### What's Still Open

- The packaged family + the metric-continuity corollary below (currently `sorry` where a
  short assembly is needed; the atomic inequalities discharge by the cited lemmas).

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**restatement / curated bundle with corollary**.

## Target Lean Sketch

```lean
variable {α : Type*} [PseudoMetricSpace α]

/-- Reverse triangle inequality. -/
theorem reverse_triangle (x y z : α) : |dist x z - dist y z| ≤ dist x y :=
  abs_dist_sub_le x y z

/-- Quadrilateral reverse inequality (move both endpoints). -/
theorem reverse_triangle_quad (x y x' y' : α) :
    |dist x y - dist x' y'| ≤ dist x x' + dist y y' := by
  -- `dist_dist_dist_le` gives `dist (dist x y) (dist x' y') ≤ dist x x' + dist y y'`,
  -- and on ℝ `dist a b = |a - b|`.
  simpa [Real.dist_eq] using dist_dist_dist_le x y x' y'

/-- Norm reverse triangle inequality. -/
theorem reverse_triangle_norm {E : Type*} [SeminormedAddGroup E] (a b : E) :
    |‖a‖ - ‖b‖| ≤ ‖a - b‖ := abs_norm_sub_norm_le a b

/-- The metric is 1-Lipschitz, hence continuous, in its right argument. -/
theorem dist_lipschitz (x : α) : LipschitzWith 1 (dist x) := LipschitzWith.dist_right x

example (x : α) : Continuous (dist x) := (dist_lipschitz x).continuous
```

Add worked `example`s in `ℝ` (`|(|x| - |y|)| ≤ |x - y|`) and a two-point perturbation showing
the quadrilateral bound is tight.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `triangle-inequality` | Parent: forward triangle inequality | metric spaces |
| `cauchy-schwarz` | Underlies the norm triangle inequality | inner products |
| `minkowski-theorem` | `L^p` triangle inequality context | normed spaces |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 5/10  |  **Tractability**: 9/10  |  **Tier**: B

**Justification**: The atomic inequalities are direct Mathlib lemmas; the only assembly is
the quadrilateral form (`dist_dist_dist_le` + `Real.dist_eq`) and the continuity corollary
(`LipschitzWith.continuous`). A clean, fully verifiable bundle.

### Suggested First Steps

1. Restate `abs_dist_sub_le` and `abs_norm_sub_norm_le` as the reverse forms.
2. Derive the quadrilateral inequality from `dist_dist_dist_le` via `Real.dist_eq`.
3. Package `LipschitzWith.dist_right` and derive `Continuous (dist x)`; add ℝ examples.

## References

### Mathlib

- `abs_dist_sub_le`, `dist_dist_dist_le` — Topology/MetricSpace/Pseudo/Defs.lean
- `abs_norm_sub_norm_le`, `norm_sub_norm_le` — Analysis/Normed/Group/Basic.lean
- `LipschitzWith.dist_right`, `LipschitzWith.dist_left` — Topology/MetricSpace/Lipschitz.lean

### Literature

- The reverse (second) triangle inequality; standard in any metric-space / normed-space text.

## Metadata

```yaml
tags:
  - metric-spaces
  - triangle-inequality
  - lipschitz
  - normed-groups
related_proofs:
  - triangle-inequality
  - cauchy-schwarz
  - minkowski-theorem
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
