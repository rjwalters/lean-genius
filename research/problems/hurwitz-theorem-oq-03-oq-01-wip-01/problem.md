# Problem: Complete Hurwitz Only-If: Normed Division Algebras via Gelfand-Mazur

**Slug**: hurwitz-theorem-oq-03-oq-01-wip-01
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
A \text{ a normed division algebra over } \mathbb{R} \text{ with a multiplicative norm} \implies \dim_{\mathbb{R}} A \in \{1, 2, 4, 8\},\ A \cong \mathbb{R}, \mathbb{C}, \mathbb{H}, \text{ or } \mathbb{O}.
$$
This WIP targets the commutative (field) case: any normed field over $\mathbb{R}$ is $\mathbb{R}$ or $\mathbb{C}$.

### Plain Language

Hurwitz's theorem classifies the real normed division algebras — there are exactly
four (the reals, complexes, quaternions, octonions). The "only-if" direction says no
others can exist. This work-in-progress handles the commutative case: a normed field
extension of R must be R or C (dimension 1 or 2), proved via the Gelfand-Mazur
theorem. The genuinely non-commutative case (quaternions H) needs Clifford-algebra
representation theory and is out of scope here.

### Why This Matters

The four normed division algebras are foundational across algebra, geometry, and
physics. A formal, Gelfand-Mazur-based proof of the commutative sub-case exercises
Mathlib's Banach-algebra spectral theory and provides a clean, reusable statement.

## Known Results

### What's Already Proven

- The source entry `hurwitz-theorem-oq-03-oq-01` proves the commutative case via
  Gelfand-Mazur: any normed field over R is isomorphic to R or C.
- Gelfand-Mazur (a normed division C-algebra is C) is available in Mathlib.

### What's Still Open

- Discharging the remaining `sorry`s tying the field case together cleanly.
- The non-commutative (H) case via Clifford algebra representation theory.

### Our Goal

Complete the work-in-progress source proof `hurwitz-theorem-oq-03-oq-01`: close the
remaining gaps in the commutative Gelfand-Mazur argument (dimension 1 or 2), without
attempting the non-commutative octonion/quaternion extension.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| hurwitz-theorem-oq-03-oq-01 | Direct parent WIP proof being completed | Gelfand-Mazur, normed fields |
| hurwitz-theorem | Base classification statement | division algebras, norms |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Apply Mathlib's Gelfand-Mazur to the complexification.
   - Why it might work: Reduces the field case to a known spectral-theory result.
   - Risk: Bookkeeping between the real algebra and its complexification.

2. **Approach B**: Direct minimal-polynomial / algebraicity argument.
   - Why it might work: A normed field over R is algebraic of degree ≤ 2.
   - Risk: Formalizing the norm-multiplicativity ⇒ algebraic step.

### Key Difficulties

- Relating the real normed field to Mathlib's complex Gelfand-Mazur statement.
- Handling the isomorphism (not just dimension) cleanly.

### What Would a Proof Need?

- Key lemma 1: A normed field over R embeds in / complexifies to a normed C-algebra.
- Key lemma 2: Gelfand-Mazur forces dimension 1 or 2 and the R/C isomorphism.
- Technical requirements: Mathlib Banach-algebra spectrum and field-extension API.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The commutative case leans on an existing Mathlib theorem (Gelfand-Mazur).
- The main effort is glue and the R↔C bookkeeping, not new deep theory.
- The non-commutative case is deliberately excluded to keep scope tractable.

**Estimated Effort**:
- Exploration: hours
- If tractable: days
- If hard: 1 week

## References

### Papers
- Hurwitz, "Über die Komposition der quadratischen Formen", 1898 — original.

### Online Resources
- Standard notes on Gelfand-Mazur and the classification of normed division algebras.

### Mathlib
- `Mathlib.Analysis.Normed.Algebra.GelfandMazur` — Gelfand-Mazur theorem.
- `Mathlib.Analysis.Normed.Field.*` — normed field API.

## Metadata

```yaml
tags:
  - algebra
  - normed-algebras
  - division-algebras
  - gelfand-mazur
  - hurwitz-theorem
related_proofs:
  - hurwitz-theorem-oq-03-oq-01
  - hurwitz-theorem
difficulty: medium
source: gallery-gap
created: 2026-07-04
```
