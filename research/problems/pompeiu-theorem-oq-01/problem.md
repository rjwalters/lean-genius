# Problem: Pompeiu's Theorem

**Slug**: pompeiu-theorem-oq-01
**Created**: 2026-06-16T06:50:00-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $ABC$ be an equilateral triangle and $P$ an arbitrary point in the plane.
Then the three lengths $PA$, $PB$, $PC$ satisfy the triangle inequalities, i.e.
they are the side lengths of a (possibly degenerate) triangle:
$$
PA \le PB + PC, \quad PB \le PA + PC, \quad PC \le PA + PB,
$$
and the triangle is degenerate (equality in one inequality) **iff** $P$ lies
on the circumcircle of $ABC$.

### Plain Language

Take an equilateral triangle and any point $P$. Measure the three distances
from $P$ to the corners. Those three distances can always be used as the side
lengths of a triangle — and that triangle is flat (degenerate) exactly when
$P$ sits on the circle through the three corners.

### Why This Matters

Pompeiu's theorem is a clean, surprising result tying the equilateral triangle
to the triangle inequality, with a slick complex-number proof. It is a natural
turnkey target that exercises Mathlib's complex-modulus and metric API and
complements the gallery's complex-coordinate triangle proofs.

## Known Results

### What's Already Proven

- Complex modulus / triangle inequality — `Complex.abs`, `abs_add`,
  `norm_add_le`, `dist` API (Mathlib).
- Roots of unity / equilateral characterization — `Complex.isPrimitiveRoot`
  and `ω = e^{2πi/3}` machinery (Mathlib).

### What's Still Open

- No formalization of Pompeiu's theorem in Mathlib or the gallery.
- The degenerate-iff-concyclic refinement is unformalized.

### Our Goal

Formalize the core triangle inequality for $PA, PB, PC$ when $ABC$ is
equilateral, and (stretch) the degeneracy ⇔ concyclicity characterization.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| ptolemys-theorem | Distance identities on concyclic points via complex numbers | complex numbers |
| napoleons-theorem | Equilateral-triangle construction in complex coordinates | complex coordinates |
| varignon-theorem | Turnkey complex-coordinate plane geometry | complex numbers, ring identity |

## Initial Thoughts

### Potential Approaches

1. **Complex numbers with cube roots of unity**: Place $A, B, C$ at $1, \omega,
   \omega^2$ (cube roots of unity), $P$ at $z$. The key identity
   $(z-1) + \omega(z-\omega) + \omega^2(z-\omega^2)$-style relation, combined
   with $|x| + |y| \ge |x+y|$, yields the triangle inequality on
   $|z-1|, |z-\omega|, |z-\omega^2|$.
   - Why it might work: the proof reduces to the standard triangle inequality
     applied to a vanishing-sum of three complex numbers — exactly the turnkey
     identity style used in Varignon/British Flag.
   - Risk: the equality/degeneracy case requires identifying when the three
     complex terms are positively collinear (⇔ $P$ on circumcircle).

2. **Ptolemy inequality**: Pompeiu follows from the general Ptolemy inequality
   applied to the cyclic/non-cyclic quadrilateral $PABC$ with the equilateral
   constraint $AB = BC = CA$.
   - Why it might work: if a Ptolemy inequality is available, this is short.
   - Risk: Mathlib may not have the Ptolemy *inequality* (only the equality on
     concyclic points, if that).

### Key Difficulties

- The equality/degeneracy characterization (concyclic ⇔ degenerate) needs the
  positive-collinearity condition for the complex triangle inequality.
- Encoding "equilateral" cleanly (via cube roots of unity vs. metric equalities).

### What Would a Proof Need?

- The vanishing linear combination of $z - \omega^k$ with unit coefficients.
- The complex triangle inequality `Complex.abs_add` / `norm_add_le`.
- Equality condition of the triangle inequality for the degeneracy claim.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Forward inequality is a direct application of the complex triangle inequality
  to a vanishing sum — closely matching completed turnkey complex-coordinate
  gallery proofs.
- Only the degeneracy ⇔ concyclic refinement adds difficulty.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days
- If hard: up to 1 week (degeneracy characterization)

## References

### Papers
- D. Pompeiu (1936); see Coxeter & Greitzer, *Geometry Revisited*.

### Online Resources
- https://en.wikipedia.org/wiki/Pompeiu%27s_theorem — statement and complex proof.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle` (roots of unity).
- `Mathlib.Analysis.Normed.Field.Basic` (`norm_add_le`, triangle inequality).
- `Mathlib.Geometry.Euclidean.Sphere.Basic` (circumcircle / concyclicity).

## Metadata

```yaml
tags:
  - euclidean-geometry
  - triangle-geometry
  - complex-numbers
related_proofs:
  - ptolemys-theorem
  - napoleons-theorem
  - varignon-theorem
difficulty: medium
source: gallery-gap
created: 2026-06-16T06:50:00-07:00
```
