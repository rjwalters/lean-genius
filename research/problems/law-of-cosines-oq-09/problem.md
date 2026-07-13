# Problem: Acute-Right-Obtuse Trichotomy from the Law of Cosines (Euclid II.12 and II.13)

**Slug**: law-of-cosines-oq-09
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: law-of-cosines

## Problem Statement

### Formal Statement

For the angle $C$ opposite side $c$ in a triangle with sides $a,b,c$:
$$
C < \tfrac{\pi}{2} \iff a^2+b^2 > c^2,\qquad
C = \tfrac{\pi}{2} \iff a^2+b^2 = c^2,\qquad
C > \tfrac{\pi}{2} \iff a^2+b^2 < c^2.
$$
Coordinate-free: the unoriented angle between vectors $x,y$ is $<,=,>\ \tfrac{\pi}{2}$
exactly as $\langle x,y\rangle$ is $>,=,<\ 0$.

### Plain Language

The Law of Cosines $c^2 = a^2+b^2-2ab\cos C$ makes classifying a triangle's angle a purely
algebraic test on side lengths: the angle opposite $c$ is acute, right, or obtuse exactly
as $a^2+b^2$ exceeds, equals, or falls short of $c^2$. This is precisely Euclid's case
split in *Elements* Book II Propositions 12 (obtuse) and 13 (acute), which the parent
entry's history discusses but does not formalize. We prove the coordinate-free trichotomy
in any real inner-product space and derive the triangle-side form from Mathlib's `law_cos`.

### Why This Matters

Siblings cover spherical (oq-01), hyperbolic (oq-03), Stewart/median (oq-04), Apollonius/
parallelogram (oq-07), and the triangle inequality (oq-08). None formalizes the acute/
right/obtuse sign trichotomy, and Mathlib has no direct "angle vs π/2 iff inner sign"
lemma (only the right-angle equality case), so this is a genuine gap.

## Known Results

### What's Already Proven

- Parent `law-of-cosines` is verified (0-axiom).
- Mathlib has `InnerProductGeometry.cos_angle_mul_norm_mul_norm`, `angle_nonneg`,
  `angle_le_pi`, `Real.strictAntiOn_cos`, `EuclideanGeometry.law_cos`.

### What's Still Open

- The target theorems below (currently `sorry`).

### Our Goal

Prove the sketch below as a verified (0-axiom) child. Category: **specialization /
characterization**.

## Target Lean Sketch

```lean
open InnerProductGeometry Real
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem angle_lt_pi_div_two_iff_inner_pos {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    angle x y < π / 2 ↔ 0 < ⟪x, y⟫_ℝ := by
  sorry -- cos_angle_mul_norm_mul_norm + strictAntiOn_cos on [0,π] + cos_pi_div_two

theorem pi_div_two_lt_angle_iff_inner_neg {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    π / 2 < angle x y ↔ ⟪x, y⟫_ℝ < 0 := by
  sorry -- symmetric to the above

-- Affine (triangle-side) form, Euclid II.12 / II.13:
theorem angle_obtuse_iff_dist_sq_lt {P : Type*} [MetricSpace P] [NormedAddTorsor V P]
    {p₁ p₂ p₃ : P} (h12 : p₁ ≠ p₂) (h32 : p₃ ≠ p₂) :
    π / 2 < ∠ p₁ p₂ p₃ ↔ dist p₁ p₂ ^ 2 + dist p₃ p₂ ^ 2 < dist p₁ p₃ ^ 2 := by
  sorry -- law_cos expresses dist p₁ p₃ ^2 via cos ∠; nlinarith on positive factor
```

Plus the acute (`<`) and right (`=`) affine companions and worked examples (3-4-5 right
triangle; an obtuse triangle) checked by `norm_num`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `law-of-cosines` | Parent: Law of Cosines | inner products, angles |
| `law-of-cosines-oq-08` | Sibling: triangle inequality | angle/norm bounds |
| `pythagorean-theorem` | Right-angle special case | inner products |

## Tractability Assessment

**Difficulty**: Low-Medium

**Significance**: 6/10  |  **Tractability**: 7/10  |  **Tier**: B

**Justification**: Every step is a named Mathlib lemma plus `linarith`/`nlinarith` sign
arithmetic; no analysis or new definitions. The angle lies in $[0,\pi]$ where $\cos$ is
strictly decreasing, so cos-sign converts to angle-vs-$\pi/2$ directly.

### Suggested First Steps

1. Use `cos_angle_mul_norm_mul_norm` to reduce inner-product sign to $\cos(\text{angle})$
   sign (the norm product is positive for nonzero vectors).
2. Apply `Real.strictAntiOn_cos` on `[0,π]` with `cos_pi_div_two = 0` to convert to the
   angle comparison; reuse `inner_eq_zero_iff_angle_eq_pi_div_two` for the right case.
3. For the affine form, apply `law_cos` and transfer the cos-sign via `nlinarith` using the
   positive factor `2 * dist p₁ p₂ * dist p₃ p₂`.

## References

### Mathlib

- `InnerProductGeometry.cos_angle_mul_norm_mul_norm`, `angle_nonneg`, `angle_le_pi`, `inner_eq_zero_iff_angle_eq_pi_div_two` — Geometry/Euclidean/Angle/Unoriented/Basic.lean
- `Real.strictAntiOn_cos`, `Real.cos_pi_div_two` — Analysis/SpecialFunctions/Trigonometric/Basic.lean
- `EuclideanGeometry.law_cos` — Geometry/Euclidean/Triangle.lean

### Literature

- Euclid, *Elements*, Book II, Propositions 12 and 13.

## Metadata

```yaml
tags:
  - geometry
  - euclidean-geometry
  - law-of-cosines
  - inner-product-spaces
  - angles
related_proofs:
  - law-of-cosines
  - law-of-cosines-oq-08
  - pythagorean-theorem
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
