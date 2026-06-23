# Problem: Algebraic Proof of the Converse Power-of-a-Point Theorem

**Slug**: product-of-segments-of-chords-oq-02
**Created**: 2026-06-14
**Status**: Active (OBSERVE)
**Source**: gallery-gap (parent: `product-of-segments-of-chords`)

## Problem Statement

### Formal Statement

The intersecting-chords theorem (power of a point): if two chords of a circle meet at $P$, then
the products of the two segment lengths are equal, $PA\cdot PB = PC\cdot PD$. The parent gallery
proof formalizes this **forward** direction and *axiomatizes* the **converse**:

$$
PA\cdot PB = PC\cdot PD \ \text{(with $A,B,C,D$ suitably placed)} \implies A,B,C,D\ \text{concyclic}.
$$

This problem asks to **discharge that axiom** — prove the converse algebraically inside the
formalization, avoiding the synthetic "construct the circle through three points and show the
fourth lies on it" argument.

### Plain Language

If two chords cross inside a circle, the pieces multiply to the same value on both chords. The
gallery proves that. The *converse* — that the equal-products condition forces the four points to
lie on a common circle — is currently assumed (an axiom). The goal is to prove it directly from
coordinates/algebra, removing the assumption and making the entry axiom-free.

### Why This Matters

Removing an axiom turns a `axiomatized` entry into a fully `verified` one — a direct integrity
improvement for the gallery. The converse is the basis of the radical-axis and power-of-a-point
toolkit; an algebraic (coordinate or determinant) proof is reusable for related concyclicity
results (Ptolemy, radical axis, the converse of the tangent-secant theorem).

## Known Results

### What's Already Proven

- `product-of-segments-of-chords` — forward intersecting-chords theorem (parent); converse currently an axiom.
- Mathlib: `EuclideanGeometry`, `Sphere`/`Circle` membership, `EuclideanGeometry.mul_dist_eq...` power-of-a-point lemmas, `Cospherical`/`Concyclic` predicates.

### What's Still Open (in this gallery)

- An algebraic/coordinate proof of the converse (concyclicity from equal products) replacing the axiom.
- `axiomCount` for this entry reduced to $0$ as a result.

### Our Goal

Prove the converse: given $P$, lines through $P$ meeting the configuration at $A,B$ and $C,D$ with
$\overline{PA}\cdot\overline{PB} = \overline{PC}\cdot\overline{PD}$ (signed powers equal), conclude
$A,B,C,D$ are concyclic — via the determinant/general-circle-equation criterion — and delete the
axiom from the parent file.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| product-of-segments-of-chords | Direct parent; supplies the forward theorem and the axiom to remove | power of a point, similar triangles |
| ptolemys-theorem (gallery) | Concyclicity criteria and chord-length relations | cyclic quadrilaterals |
| pascals-hexagon | Conic/concyclicity via algebraic incidence | projective/algebraic geometry |

## Initial Thoughts

### Potential Approaches

1. **General circle equation / determinant (recommended)**: four points are concyclic iff the
   $4\times4$ "concyclicity determinant" vanishes; show the equal-power hypothesis forces it.
   - Why it might work: pure algebra, no synthetic circle construction; matches Mathlib's coordinate geometry.
   - Risk: translating the *signed* power condition and collinearity-through-$P$ into the determinant cleanly.

2. **Radical-axis / power-function approach**: define the power of $P$ w.r.t. the unique circle through $A,B,C$ and show $D$ has the same power, hence lies on it.
   - Why it might work: conceptually direct; reuses power-of-a-point.
   - Risk: "unique circle through three non-collinear points" existence/uniqueness must be available or proved.

### Key Difficulties

- Handling signed lengths / directed ratios so the converse holds with correct orientation hypotheses.
- Degenerate cases (collinear triples, $P$ on the circle, tangent configurations).

### What Would a Proof Need?

- Key lemma 1: concyclicity ⇔ vanishing of the general-circle determinant for four planar points.
- Key lemma 2: equal signed power of $P$ ⇒ that determinant vanishes.
- Technical requirements: `EuclideanGeometry`, `Matrix.det`, `Cospherical`/`Concyclic`, inner-product distance lemmas.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The converse is a finite algebraic identity once the determinant criterion is set up.
- Mathlib's Euclidean geometry has the needed power-of-a-point and cospherical infrastructure.
- Care with signs and degeneracies is the main cost; the payoff (axiom removal) is concrete.

**Estimated Effort**:
- Exploration: days
- If tractable: 1–2 weeks
- If hard: 3–4 weeks (if uniqueness-of-circle and sign conventions prove fiddly)

## References

### Papers
- Euclid, *Elements* III.35–36 — intersecting chords and converse.
- Coxeter & Greitzer, *Geometry Revisited* — power of a point, radical axis.

### Online Resources
- Parent gallery entry `product-of-segments-of-chords`.

### Mathlib
- `Mathlib.Geometry.Euclidean.Sphere.Power` — power-of-a-point lemmas.
- `Mathlib.Geometry.Euclidean.Circumcenter` / `Cospherical` — concyclicity.

## Metadata

```yaml
tags:
  - geometry
  - euclidean-geometry
  - power-of-a-point
  - axiom-elimination
related_proofs:
  - product-of-segments-of-chords
  - ptolemys-theorem
  - pascals-hexagon
difficulty: medium
source: proof-suggestion
created: 2026-06-14
```
