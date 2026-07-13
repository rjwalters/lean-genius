# Problem: Carnot's Theorem (signed distances to the sides)

**Slug**: carnot-theorem-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $ABC$ be a triangle with circumradius $R$, inradius $r$, and circumcenter
$O$. Let $d_a, d_b, d_c$ be the **signed** distances from $O$ to the sides
$BC$, $CA$, $AB$ (a distance is negative when $O$ lies on the far side of the
line from the triangle interior, i.e. for an obtuse triangle). Then

$$
d_a + d_b + d_c = R + r .
$$

Equivalently, with $d_a = R\cos A$, $d_b = R\cos B$, $d_c = R\cos C$, this is

$$
\cos A + \cos B + \cos C = 1 + \frac{r}{R}.
$$

### Plain Language

Add up the (signed) distances from the center of a triangle's circumscribed
circle to its three sides. The total always equals the circumradius plus the
inradius. The signed convention is what makes the identity survive obtuse
triangles, where the circumcenter falls outside the triangle.

### Why This Matters

Carnot's theorem ties the two principal circles of a triangle (circumcircle and
incircle) together through a clean additive relation. It is a natural companion
to the gallery's existing triangle proofs (Heron, Napoleon, Routh, Menelaus)
and exercises Mathlib's distance/projection API together with the
$\cos A + \cos B + \cos C = 1 + r/R$ trigonometric route.

## Known Results

### What's Already Proven

- Law of cosines and angle machinery — `EuclideanGeometry.law_cos`,
  `EuclideanGeometry.angle` (Mathlib).
- Orthogonal projection / signed distance to an affine line —
  `EuclideanGeometry.orthogonalProjection` (Mathlib).
- Triangle area / inradius / circumradius relations ($r = \text{Area}/s$,
  $R = abc/4\,\text{Area}$) derivable from existing area lemmas.

### What's Still Open

- No formalization of Carnot's theorem in Mathlib or the gallery.
- The signed-distance bookkeeping in the obtuse case is the only subtle point.

### Our Goal

Formalize $\cos A + \cos B + \cos C = 1 + r/R$ (algebraic, from half-angle /
product relations), then connect to $d_a + d_b + d_c = R + r$ via
$d_a = R\cos A$. A self-contained coordinate proof on $\mathbb{R}\times\mathbb{R}$
(circumcenter at origin, vertices on a radius-$R$ circle) is an acceptable
alternative if the Euclidean API proves heavy.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| herons-formula | triangle area / side relations | coordinate, ring |
| napoleons-theorem | circumcenter constructions | complex numbers |
| routh-theorem | cevian/area ratios | determinant, ring |

## Initial Thoughts

### Potential Approaches

1. **Trig identity route**: prove $\cos A+\cos B+\cos C = 1+r/R$ using
   $r/R = 4\sin\tfrac{A}{2}\sin\tfrac{B}{2}\sin\tfrac{C}{2}$ and $A+B+C=\pi$.
   - Why it might work: reduces to one `nlinarith`/`ring` identity.
   - Risk: half-angle substitution bookkeeping.

2. **Coordinate route**: place $O$ at origin, $A,B,C$ on circle of radius $R$;
   foot of perpendicular from $O$ to $BC$ has signed length $R\cos A$.
   - Why it might work: fully elementary, `ring`-friendly.
   - Risk: relating $r$ to the coordinates still needs the area formula.

### Key Difficulties

- Encoding the *signed* distance correctly (sign flips for obtuse angle).
- Linking $r/R$ to the chosen coordinates/angles.

### What Would a Proof Need?

- Lemma: signed distance $O\to BC$ equals $R\cos A$.
- Lemma: $\cos A+\cos B+\cos C = 1 + r/R$.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- Classical identity reducible to a single trigonometric equation.
- Mathlib has law of cosines, projection, and area lemmas.
- Comparable in scope to the already-formalized Menelaus/Routh proofs.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Papers
- L. N. M. Carnot, *Géométrie de position* (1803) — original signed-distance identity.

### Online Resources
- Standard triangle-geometry references for $\cos A+\cos B+\cos C = 1+r/R$.

### Mathlib
- `Mathlib.Geometry.Euclidean.Angle` — law of cosines, angle API.
- `Mathlib.Geometry.Euclidean.Projection` — orthogonal projection / distances.

## Metadata

```yaml
tags:
  - euclidean-geometry
  - triangle-geometry
  - coordinate-geometry
related_proofs:
  - herons-formula
  - routh-theorem
difficulty: medium
source: gallery-gap
created: 2026-06-16
```
