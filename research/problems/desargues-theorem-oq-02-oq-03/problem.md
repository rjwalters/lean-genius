# Problem: Desargues' Theorem over Free Rank-3 Modules on Non-Commutative Rings

**Slug**: desargues-theorem-oq-02-oq-03
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $R$ be a (possibly non-commutative) ring and $M = R^3$ a free left $R$-module of rank 3, with the associated projective plane $\mathbb{P}(M)$ of rank-1/rank-2 submodules. Determine the precise conditions on $R$ under which the **Desargues configuration** holds: if two triangles are perspective from a point, they are perspective from a line.

$$
\text{Desargues holds in } \mathbb{P}(R^3) \iff R \text{ is a division ring (skew field).}
$$

### Plain Language

The parent proof `desargues-theorem-oq-02` exhibits the **Moulton plane**, a non-Desarguesian projective plane, as a counterexample showing Desargues' theorem fails without a coordinatizing division ring. This problem investigates the positive/coordinatized direction: over a free rank-3 module on a non-commutative ring, when does Desargues hold? The classical answer (the **coordinatization theorem** of projective geometry) is that Desargues holds exactly when the plane is coordinatized by a division ring — commutativity of $R$ is *not* required (that governs Pappus, not Desargues).

### Why This Matters

The Desargues ⇔ division-ring equivalence is the foundational bridge between synthetic projective geometry and linear algebra, and separates cleanly from the Pappus ⇔ field (commutative) result. Formalizing it clarifies the exact algebraic hypotheses and complements the gallery's Moulton-plane counterexample with the structural theorem.

## Known Results

### What's Already Proven
- Moulton plane is non-Desarguesian — gallery `desargues-theorem-oq-02`.
- Desargues in $\mathbb{P}^2$ over a field — classical; partial Mathlib projective-geometry API.

### What's Still Open (for formalization)
- Desargues for $\mathbb{P}(R^3)$ with $R$ a non-commutative division ring.
- The converse: failure of Desargues ⇒ non-division-ring coordinatization.

### Our Goal
Formalize the forward direction: over a division ring $R$ (allowing non-commutative), Desargues' theorem holds in $\mathbb{P}(R^3)$. Clarify precisely where the division-ring hypothesis (existence of inverses) enters and why commutativity is unnecessary.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| desargues-theorem-oq-02 | Direct parent; counterexample side | Moulton plane |
| desargues-theorem-oq-01 | Sibling generalization | Incidence geometry |

## Initial Thoughts

### Potential Approaches
1. **Linear-algebra coordinates**: represent points as rank-1 submodules of $R^3$; carry out the standard determinant-free perspectivity computation, being careful to keep scalars on a consistent side (left vs right multiplication) since $R$ is non-commutative.
2. **Synthetic + coordinatization**: invoke the abstract coordinatization theorem, if a usable projective-plane axiomatization is available.

### Key Difficulties
- Non-commutativity forces care with left/right scalar actions; the classical determinant proof must be replaced with an inverse-based argument.
- Mathlib's projective-space API (`Projectivization`) is built for division rings but the Desargues statement itself may need to be set up from scratch.

### What Would a Proof Need?
- A workable incidence/projective-plane model over $R^3$.
- The perspectivity computation using only $R$-inverses (no commutativity).

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**: Mathematically classical and well-understood, but the Lean projective-geometry infrastructure for Desargues specifically appears thin; setup cost is the main risk rather than the mathematics.

## References

### Texts
- Hartshorne, *Foundations of Projective Geometry*.// Artin, *Geometric Algebra* (Desargues ⇔ division ring).

### Mathlib
- `Projectivization`, `Module`, `DivisionRing`, incidence structures.

## Metadata

```yaml
tags:
  - projective-geometry
  - incidence-geometry
  - non-commutative-algebra
  - desargues
related_proofs:
  - desargues-theorem-oq-02
  - desargues-theorem-oq-01
difficulty: high
source: gallery-gap
created: 2026-07-04
```
