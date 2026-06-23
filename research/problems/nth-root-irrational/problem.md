# Problem: Algebraic Irrationality via Irreducible Polynomials

**Slug**: nth-root-irrational
**Created**: 2026-03-11
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{If } p(x) \in \mathbb{Z}[x] \text{ is irreducible over } \mathbb{Q} \text{ and } \deg(p) \geq 2, \text{ then all roots of } p \text{ are irrational.}
$$

### Plain Language

If a polynomial with integer coefficients cannot be factored over the rationals and has degree at least 2, then none of its roots are rational numbers. This generalizes the irrationality of √n (which uses the polynomial x² - n) to arbitrary algebraic numbers.

### Why This Matters

This is the natural generalization of nth-root irrationality. Rather than proving irrationality case by case (√2, √3, ∛5, ...), we prove a single theorem that covers all at once via the Rational Root Theorem and polynomial irreducibility.

## Known Results

### What's Already Proven

- Irrationality of nth roots of non-perfect-powers — `nth-root-irrational` gallery proof
- Rational Root Theorem — likely in Mathlib
- Polynomial irreducibility testing — Eisenstein criterion in Mathlib

### What's Still Open

- General algebraic irrationality theorem in Lean
- Connection to irreducibility criteria (Eisenstein, etc.)

### Our Goal

Prove: if p ∈ ℤ[x] is irreducible over ℚ with deg(p) ≥ 2, then p has no rational roots. Then show nth-root irrationality follows as a corollary.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| nth-root-irrational | Direct parent — special case | Contradiction, divisibility |
| sqrt2-irrational | Simplest case | Classic proof by contradiction |
| fundamental-arithmetic | Unique factorization | Ring theory |

## Initial Thoughts

### Potential Approaches

1. **Rational Root Theorem**: If p/q is a root of aₙxⁿ + ... + a₀, then p | a₀ and q | aₙ. For irreducible polynomial of degree ≥ 2, any rational root gives a linear factor, contradicting irreducibility.
   - Why it might work: Completely elementary, Mathlib likely has the pieces
   - Risk: Need to connect Polynomial.Irreducible to "no linear factors"

2. **Gauss's Lemma approach**: Irreducible over ℤ implies irreducible over ℚ (for primitive polynomials). A rational root means a linear factor over ℚ.
   - Why it might work: More general, uses Gauss's lemma from Mathlib
   - Risk: May need primitive polynomial handling

### Key Difficulties

- Connecting `Polynomial.Irreducible` to the non-existence of linear factors
- Ensuring the degree condition is properly handled

### What Would a Proof Need?

- Key lemma 1: Rational Root Theorem (p/q root → p | a₀, q | aₙ)
- Key lemma 2: Rational root → linear factor
- Key lemma 3: Irreducible + degree ≥ 2 → no linear factors
- Technical requirements: Polynomial ring theory in Mathlib

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Rational Root Theorem is elementary
- Mathlib has extensive polynomial ring theory
- The logical chain is short and well-understood
- Similar in spirit to existing gallery proofs

## References

### Mathlib
- `Mathlib.RingTheory.Polynomial.RationalRoot` — Rational Root Theorem
- `Mathlib.RingTheory.Polynomial.Eisenstein` — Eisenstein criterion
- `Mathlib.RingTheory.Polynomial.GaussLemma` — Gauss's Lemma

## Metadata

```yaml
tags:
  - algebra
  - irrationality
  - polynomials
  - number-theory
related_proofs:
  - nth-root-irrational
  - sqrt2-irrational
  - fundamental-arithmetic
difficulty: medium
source: gallery-gap
created: 2026-03-11
```
