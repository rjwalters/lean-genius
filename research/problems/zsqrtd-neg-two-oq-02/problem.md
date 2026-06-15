# Problem: Legendre–Gauss three-square theorem via the ℤ[√−2] infrastructure

**Slug**: zsqrtd-neg-two-oq-02
**Created**: 2026-06-15T06:15:07.078468+00:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall n \in \mathbb{N}:\quad \big(\exists a,b,c \in \mathbb{Z},\ n = a^2 + b^2 + c^2\big)\ \iff\ \neg\big(\exists a,b \in \mathbb{N},\ n = 4^{a}(8b + 7)\big)
$$

### Plain Language

Building on the gallery's ℤ[√−2] development (a Euclidean domain whose norm form is x² + 2y²), formalize the full Legendre–Gauss three-square theorem: a natural number n is a sum of three integer squares if and only if n is NOT of the form 4ᵃ·(8b + 7). The forward direction (the 4ᵃ(8b+7) obstruction) is an elementary congruence argument modulo 8; the converse is the deep direction, classically proved via ternary quadratic forms or Dirichlet's theorem on primes in arithmetic progressions.

### Why This Matters

Completes the classical sums-of-squares trilogy (two squares, three squares, four squares) and exercises the quadratic-form / ANT machinery already present for x² + 2y².

## Classification

```yaml
tier: B
significance: 7
tractability: 4
```

**Significance**: 7/10
**Tractability**: 4/10

## Known Results

### What's Already Proven

- Lagrange four-square theorem (in Mathlib).
- Fermat two-square theorem and the x² + 2y² representation theory (gallery ℤ[√−2] file).
- The forward obstruction: numbers ≡ 7 (mod 8), and 4ᵃ(8b+7), are not sums of three squares (mod-8 argument).

### What's Still Open

- The converse direction in Lean: every n not of the form 4ᵃ(8b+7) IS a sum of three squares.
- Whether to route via ternary forms or via Dirichlet's theorem on primes in AP.

### Our Goal

Formalize the full iff; the forward direction is elementary, the converse is the substantive deliverable.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| zsqrtd-neg-two | Parent gallery proof this open question extends |

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Forward direction is a short mod-8 congruence proof.
- Converse needs ternary quadratic forms or Dirichlet-in-AP, both heavy; this is the hard half.
- Mathlib has Lagrange four squares and Gaussian/Euclidean-domain machinery to build on.

## Metadata

```yaml
tags:
  - number-theory
  - algebraic-number-theory
  - quadratic-forms
  - sums-of-squares
  - challenging
  - extension
  - gallery-extracted
  - seeker-selected
  - research
related_proofs:
  - zsqrtd-neg-two
difficulty: high
source: gallery-gap
created: 2026-06-15T06:15:07.078468+00:00
```
