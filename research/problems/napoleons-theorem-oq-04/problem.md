# Problem: Napoleon's Area Theorem (Outer minus Inner equals the Original)

**Slug**: napoleons-theorem-oq-04
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: napoleons-theorem

## Problem Statement

### Formal Statement

For any triangle $z_1,z_2,z_3\in\mathbb C$, let $G_1,G_2,G_3$ be the centroids of the
**outward** equilateral triangles on the sides and $G_1',G_2',G_3'$ those of the
**inward** equilateral triangles. Then

$$
\operatorname{Area}(G_1,G_2,G_3)\;-\;\operatorname{Area}(G_1',G_2',G_3')
\;=\;\operatorname{Area}(z_1,z_2,z_3),
$$

where signed area is $\operatorname{Area}(a,b,c)=\tfrac12\,\operatorname{Im}\big(\overline{(b-a)}\,(c-a)\big)$.

### Plain Language

The parent entry `napoleons-theorem` proves that the outer Napoleon triangle
`(G₁,G₂,G₃)` is equilateral (and, in a sibling result, that its centroid coincides with the
centroid of the original). This child proves the second half of the classical Napoleon
package: the **area identity**. Both the outer and inner Napoleon triangles are equilateral,
and the *difference* of their areas is exactly the area of the triangle you started with.
Because the outer triangle is always at least as large as the inner one, this also re-proves
that the outer Napoleon triangle dominates the inner one in area.

### Why This Matters

The equilaterality statement (parent) and the area statement (this child) are the two halves
of "Napoleon's theorem" as stated in the literature; Mathlib formalizes neither the area form
nor the complex-coordinate signed-area function specialised to these centroid points. The
identity is a clean polynomial cancellation once areas are expanded via
`Complex.mul_im`/`Complex.mul_re`, but it is emphatically **not** a single Mathlib lemma —
it requires assembling the area formula for three different triangles and a `ring`-level
cancellation using the explicit apex formulas.

## Known Results

### What's Already Proven

- Parent `napoleons-theorem` is verified (0-axiom): the outer Napoleon triangle is
  equilateral; a sibling proves centroid coincidence (`napoleon_centroid_eq_original`).
- Mathlib: `Complex.mul_im`, `Complex.mul_re`, `Complex.sub_im`, `Complex.add_im`,
  `Complex.conj_im` — the componentwise arithmetic needed to expand signed areas.

### What's Still Open

- The area identity below (currently `sorry`). No Mathlib lemma packages Napoleon areas or a
  complex signed-area function for these apex points.

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**geometry / identity completion**.

## Target Lean Sketch

```lean
open Complex

/-- Signed area of the triangle `a b c` via the imaginary part of a cross product. -/
noncomputable def triArea (a b c : ℂ) : ℝ :=
  (((b - a) * conj (c - a)).im) / 2

/-- Outward apex centroid on side `pq`: rotate `q-p` by +60° about the midpoint.
    Concretely `Gₒ p q = (p + q)/2 + (q - p) * (Complex.I * Real.sqrt 3 / 2)`; the
    inward version uses `-I`. Reuse the parent's `G₁ G₂ G₃` definitions if available. -/
noncomputable def Gouter (p q : ℂ) : ℂ := (p + q)/2 + (q - p) * (I * (Real.sqrt 3 / 2))
noncomputable def Ginner (p q : ℂ) : ℂ := (p + q)/2 - (q - p) * (I * (Real.sqrt 3 / 2))

/-- Napoleon's area theorem: outer area minus inner area equals the original area. -/
theorem napoleon_area_difference (z₁ z₂ z₃ : ℂ) :
    triArea (Gouter z₂ z₃) (Gouter z₃ z₁) (Gouter z₁ z₂)
      - triArea (Ginner z₂ z₃) (Ginner z₃ z₁) (Ginner z₁ z₂)
      = triArea z₁ z₂ z₃ := by
  sorry
  -- Expand each `triArea` with `Complex.mul_im`, `Complex.sub_im`, `Complex.conj_im`,
  -- substitute the Gouter/Ginner formulas, and finish with `ring`/`nlinarith`
  -- (the √3 terms enter squared, so `Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)` closes them).
```

Add worked `example`s: an equilateral input (inner area `= 0`, outer area `=` original);
a right triangle `z₁=0, z₂=1, z₃=I`; a degenerate collinear triple (all three areas `0`).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `napoleons-theorem` | Parent: outer Napoleon triangle is equilateral | complex numbers, rotations |
| `herons-formula` | Triangle area from side lengths | Euclidean geometry, algebra |
| `morleys-theorem` | Equilateral triangle from angle trisectors | complex-coordinate geometry |

## Tractability Assessment

**Difficulty**: Medium

**Significance**: 6/10  |  **Tractability**: 7/10  |  **Tier**: B

**Justification**: A finite complex-algebra expansion: expand three signed areas, substitute
apex formulas, and cancel with `ring`/`nlinarith`. The only subtlety is handling `√3` via
`Real.sq_sqrt`. No limits, no synthetic geometry.

### Suggested First Steps

1. Fix `triArea` and the outer/inner apex definitions (or import the parent's `G₁ G₂ G₃`).
2. Prove a helper `triArea_expand` rewriting `triArea a b c` into real coordinates via
   `Complex.mul_im`, `Complex.sub_im`, `Complex.conj_im`.
3. Substitute and cancel; isolate `√3²` with `Real.sq_sqrt` before `ring`/`nlinarith`.

## References

### Mathlib

- `Complex.mul_im`, `Complex.mul_re` — Data/Complex/Basic.lean
- `Complex.sub_im`, `Complex.add_im`, `Complex.conj_im` — Data/Complex/Basic.lean
- `Real.sq_sqrt`, `Real.sqrt_nonneg` — Analysis/SpecialFunctions/Sqrt.lean

### Literature

- Coxeter & Greitzer, *Geometry Revisited*, §3.3 (Napoleon's theorem and the area relation).
- The outer-minus-inner area identity is the classical companion to the equilaterality claim.

## Metadata

```yaml
tags:
  - geometry
  - napoleons-theorem
  - complex-numbers
  - area
related_proofs:
  - napoleons-theorem
  - herons-formula
  - morleys-theorem
difficulty: medium
source: proof-suggestion
created: 2026-07-01
```
