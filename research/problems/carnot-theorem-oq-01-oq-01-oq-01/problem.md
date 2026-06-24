# Problem: Carnot Signed-Distance Form with an Explicit Circumcenter over EuclideanSpace

**Slug**: carnot-theorem-oq-01-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a triangle $ABC$ with circumcenter $O$ and circumradius $R$, Carnot's theorem states that the **signed** distances from $O$ to the three sides sum to $R + r$:

$$
d_a + d_b + d_c \;=\; R + r,
$$

where $d_a, d_b, d_c$ are the signed perpendicular distances from $O$ to sides $BC, CA, AB$ (negative when $O$ lies on the far side of a side), $r$ is the inradius, and $R$ the circumradius. The goal is the metric *signed-distance* formulation with an **explicit** circumcenter, formalized over `EuclideanSpace ℝ (Fin 2)`.

### Plain Language

Carnot's theorem relates the position of a triangle's circumcenter to its inradius and circumradius via the (signed) distances from the circumcenter to the three sides. The parent entry handles the identity in a more algebraic/projected form; this problem asks to do it "metrically": construct the circumcenter as an actual point of the Euclidean plane `EuclideanSpace ℝ (Fin 2)`, define the signed distances to the sides with correct orientation, and prove $d_a+d_b+d_c = R+r$ directly in that concrete metric setting.

### Why This Matters

A metric, explicit-circumcenter version anchors Carnot's theorem in Mathlib's `EuclideanGeometry` API (the same framework used for Euler line, nine-point circle, and Feuerbach entries), making it composable with those results rather than living in a bespoke algebraic encoding. The signed-distance bookkeeping is exactly what downstream incircle/excircle and Euler-distance ($OI^2 = R^2 - 2Rr$) formalizations need.

## Known Results

### What's Already Proven

- Parent `carnot-theorem-oq-01-oq-01` (verified): Carnot's identity in its current (algebraic / projected) gallery form.
- Mathlib: `EuclideanGeometry.circumcenter`, `Affine.Simplex.circumcenter`/`circumradius`, `EuclideanGeometry.inradius`-style data, `EuclideanSpace ℝ (Fin 2)`, signed-distance and orthogonal-projection lemmas.
- Classical: Carnot's theorem and its sign convention (a side's contribution flips when the circumcenter is on the opposite side, i.e. for obtuse triangles).

### What's Still Open

- A Lean statement using `EuclideanGeometry.circumcenter` of an explicit triangle (`Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2`) and signed distances to its sides, proving $\sum d_i = R + r$.
- A correct, reusable definition of the *signed* distance (orientation handling for obtuse triangles).

### Our Goal

Construct the triangle as an `Affine.Simplex`, take `circumcenter`/`circumradius`, define signed distances to the three side-lines with consistent orientation, and prove the sum equals $R + r$, reducing to projection identities and the law of cosines / `dist` lemmas in `EuclideanSpace`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| carnot-theorem-oq-01-oq-01 | Direct parent; Carnot identity (algebraic form) | triangle geometry |
| carnot-theorem-oq-01 | Root entry; Carnot's theorem statement | circumradius, inradius |

## Initial Thoughts

### Potential Approaches

1. **Build on Mathlib's `EuclideanGeometry.circumcenter`.** Use the `Affine.Simplex` circumcenter/circumradius API, define signed distance via orthogonal projection onto each side-line, and reduce $\sum d_i = R+r$ to trigonometric identities ($d_a = R\cos A$, etc.) already expressible through `dist` and angle lemmas.
   - Why it might work: the $d_a = R\cos A$ reduction makes the sum $R(\cos A+\cos B+\cos C) = R + r$, and $\cos A+\cos B+\cos C = 1 + r/R$ is a standard identity reachable from the law of cosines.
   - Risk: assembling the signed-distance orientation and the $\cos A+\cos B+\cos C$ identity in Mathlib's angle API; obtuse-case signs.

2. **Coordinate computation.** Place the circumcenter at the origin with vertices on a circle of radius $R$ and compute signed distances directly.
   - Why it might work: turns the problem into explicit `EuclideanSpace ℝ (Fin 2)` algebra amenable to `field_simp`/`ring` after setting coordinates.
   - Risk: choosing coordinates that keep the inradius $r$ expressible and the proof general (not just for a specific triangle).
