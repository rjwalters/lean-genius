# Problem: Steiner–Lehmus Theorem

**Slug**: steiner-lehmus-theorem-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $ABC$ be a triangle. Let $t_B$ and $t_C$ be the lengths of the internal
angle bisectors from vertices $B$ and $C$ (each measured from the vertex to the
opposite side). Then

$$
t_B = t_C \;\Longrightarrow\; b = c \quad(\text{i.e. } AB = AC),
$$

so any triangle with two equal internal angle bisectors is isosceles. Using the
standard bisector-length formula from $B$,

$$
t_B^2 = ac\left[1 - \left(\frac{b}{a+c}\right)^2\right],
$$

the claim becomes: $t_B = t_C \Rightarrow b = c$.

### Plain Language

If two of a triangle's internal angle bisectors are equal in length, the
triangle must be isosceles. The converse is trivial, but this direction
famously resisted elementary *direct* proofs — yet it falls quickly to algebra.

### Why This Matters

The Steiner–Lehmus theorem is celebrated for being hard to prove
constructively while yielding to algebra. It is an ideal formalization target:
the angle-bisector length formula plus a contradiction argument
(assume $b \neq c$, derive $t_B \neq t_C$) gives a clean, fully algebraic Lean
proof, complementing the gallery's other triangle results.

## Known Results

### What's Already Proven

- Angle-bisector length formula derivable from the law of cosines /
  Stewart-type relations (`EuclideanGeometry`, `law_cos`).
- Triangle inequality and side-positivity facts (`dist`, `Real` order lemmas).

### What's Still Open

- No formalization of the Steiner–Lehmus theorem in Mathlib or the gallery.

### Our Goal

Formalize the algebraic core: from $t_B^2 = t_C^2$ with the bisector-length
formula, derive $b = c$ over positive reals $a,b,c$ satisfying the triangle
inequalities. The cleanest path is the standard contradiction: if $b > c$ then
$t_B < t_C$, contradicting equality.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| herons-formula | triangle side/area algebra | coordinate, ring |
| menelaus-theorem | side-ratio identities | determinant, ring |

## Initial Thoughts

### Potential Approaches

1. **Bisector-length formula + sign analysis**: write $t_B^2 - t_C^2$ as
   $(c-b)\cdot Q$ with $Q>0$ on the triangle domain, then `nlinarith` forces
   $b=c$.
   - Why it might work: reduces the theorem to one factored inequality.
   - Risk: producing the explicit positive factor for `nlinarith`.

2. **Direct monotonicity**: prove $b \mapsto t_B$ strictly increasing on the
   triangle domain, so equal bisectors force equal opposite sides.
   - Risk: monotonicity may need careful `nlinarith` bounds.

### Key Difficulties

- The factorization $t_B^2 - t_C^2 = (c-b)\cdot Q$ with $Q>0$ must hold under
  the triangle inequalities; certifying $Q>0$ is the crux.

### What Would a Proof Need?

- Lemma: bisector length $t_B^2 = ac\,[1 - (b/(a+c))^2]$.
- Lemma: $t_B^2 = t_C^2 \Rightarrow b = c$ for triangle-admissible $a,b,c>0$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Fully algebraic once the bisector-length formula is in hand.
- `nlinarith`/`polyrith` suit the factored inequality.
- No new Mathlib machinery beyond the law of cosines.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days (the positive-factor certificate is the variable cost)

## References

### Papers
- C. L. Lehmus / J. Steiner (1840s) — original problem and proof.
- J. Conway & A. Ryba, *The Steiner–Lehmus angle bisector theorem* (2014).

### Online Resources
- Standard expositions of the angle-bisector length formula.

### Mathlib
- `Mathlib.Geometry.Euclidean.Angle` — law of cosines.
- `Mathlib.Tactic.Polyrith` / `nlinarith` — inequality certificates.

## Metadata

```yaml
tags:
  - euclidean-geometry
  - triangle-geometry
  - inequalities
related_proofs:
  - herons-formula
  - menelaus-theorem
difficulty: medium
source: gallery-gap
created: 2026-06-16
```
