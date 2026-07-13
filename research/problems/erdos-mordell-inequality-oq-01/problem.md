# Problem: Erdős–Mordell Inequality

**Slug**: erdos-mordell-inequality-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $ABC$ be a triangle and $P$ a point in its interior (or on the boundary).
Let $R_a = PA$, $R_b = PB$, $R_c = PC$ be the distances from $P$ to the
vertices, and let $d_a, d_b, d_c$ be the distances from $P$ to the sides
$BC$, $CA$, $AB$ respectively. Then

$$
R_a + R_b + R_c \;\ge\; 2\,(d_a + d_b + d_c),
$$

with equality if and only if $ABC$ is equilateral and $P$ is its center.

### Plain Language

For any point inside a triangle, the sum of its distances to the three corners
is at least twice the sum of its distances to the three sides. Equality only
happens for an equilateral triangle with the point at the center.

### Why This Matters

The Erdős–Mordell inequality is a famous, elegant result (conjectured by Erdős
in 1935, first proved by Mordell). It is a strong candidate for the gallery: it
connects vertex distances and side distances with a sharp constant, and admits
a clean trigonometric proof using
$R_a \ge \tfrac{c}{a} d_b + \tfrac{b}{a} d_c$ (and cyclic) followed by AM–GM.
It complements the existing inequality proofs (AM–GM, Weitzenböck) in the
gallery and exercises Mathlib's `nlinarith`/AM–GM and Euclidean distance API.

## Known Results

### What's Already Proven

- AM–GM and basic real inequalities — `Real` order lemmas, `nlinarith`,
  `inner_mul_le_norm_mul_norm` (Mathlib).
- Distance to a line / orthogonal projection — `EuclideanGeometry.orthogonalProjection`.
- The gallery already has Weitzenböck's inequality (sibling triangle inequality).

### What's Still Open

- No formalization of Erdős–Mordell in Mathlib or the gallery.

### Our Goal

Formalize the inequality $R_a + R_b + R_c \ge 2(d_a + d_b + d_c)$. The standard
route: establish the three lemmas
$a\,R_a \ge c\,d_b + b\,d_c$ (and cyclic) by projecting $P$ across the angle
bisectors, then sum and apply $x/y + y/x \ge 2$ (AM–GM). The equality case is
an optional follow-on OQ.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| weitzenbock-inequality | triangle inequality, SOS | nlinarith |
| amgm-inequality | the AM–GM step | nlinarith, convexity |

## Initial Thoughts

### Potential Approaches

1. **Trigonometric / projection route**: prove $a R_a \ge c\,d_b + b\,d_c$
   (cyclic), divide by side lengths, sum, finish with AM–GM
   $\tfrac{b}{c}d_? + \tfrac{c}{b}d_? \ge 2 d_?$.
   - Why it might work: each lemma is a short geometric/`nlinarith` fact.
   - Risk: the projection lemma needs a careful angle argument.

2. **Coordinate route**: place the triangle in $\mathbb{R}^2$ and bound
   distances directly.
   - Risk: algebra is heavier and the sharp constant is delicate.

### Key Difficulties

- The core lemma $a R_a \ge c\,d_b + b\,d_c$ (the projection inequality) is the
  substantive step; the rest is AM–GM summation.
- Stating distances-to-sides cleanly with Mathlib's projection API.

### What Would a Proof Need?

- Lemma: $a\,R_a \ge c\,d_b + b\,d_c$ (and two cyclic variants).
- Lemma: AM–GM closing step $\sum (\tfrac{b}{c}+\tfrac{c}{b}) d \ge 2\sum d$.

## Tractability Assessment

**Difficulty**: Medium–Hard

**Justification**:
- The AM–GM closing step is easy; the projection lemma is the real work.
- `nlinarith` handles the algebra once the geometric lemma is set up.
- Comparable to (somewhat harder than) the formalized Weitzenböck inequality.

**Estimated Effort**:
- Exploration: days
- If tractable: 3–7 days

## References

### Papers
- P. Erdős, problem 3740, *Amer. Math. Monthly* 42 (1935).
- L. J. Mordell & D. F. Barrow, solution, *Amer. Math. Monthly* 44 (1937).
- A. Avez / V. Komornik — short trigonometric proofs.

### Online Resources
- Standard expositions of the projection-plus-AM–GM proof.

### Mathlib
- `Mathlib.Geometry.Euclidean.Projection` — distance to a line.
- `Mathlib.Analysis.MeanInequalities` / `nlinarith` — AM–GM step.

## Metadata

```yaml
tags:
  - euclidean-geometry
  - triangle-geometry
  - inequalities
related_proofs:
  - weitzenbock-inequality
  - amgm-inequality
difficulty: hard
source: gallery-gap
created: 2026-06-16
```
