# Problem: Irrationality of ∛2

**Slug**: cube-root-2-irrational
**Created**: 2024-12-30
**Status**: Active
**Source**: proof-suggestion (from sqrt2-irrational openQuestions)

## Problem Statement

### Formal Statement

$$
\sqrt[3]{2} \notin \mathbb{Q}
$$

Equivalently: there do not exist integers $p, q$ with $q \neq 0$ such that $\left(\frac{p}{q}\right)^3 = 2$.

### Plain Language

The cube root of 2 is irrational. Unlike the square root case, the simple parity argument doesn't work here—cubing preserves parity (odd³ = odd, even³ = even), so we can't derive a contradiction from "both p and q are even."

### Why This Matters

This is a natural extension of the √2 irrationality proof and demonstrates that:
1. Different proof techniques are needed for different roots
2. The rational root theorem provides a more general approach
3. Prime multiplicity arguments generalize beyond square roots

## Known Results

### What's Already Proven

- **√2 is irrational** — In our gallery (`sqrt2-irrational`), uses parity argument
- **√n irrational for non-perfect-squares** — Generalized in same proof
- **Rational Root Theorem** — Available in Mathlib

### What's Still Open (for us)

- Formalize ∛2 irrationality in Lean 4
- Connect to the general n-th root theorem
- Document the technique difference from square roots

### Our Goal

Prove in Lean 4 that `Irrational (2 : ℝ) ^ (1/3 : ℝ)` or equivalent formulation.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sqrt2-irrational | Direct predecessor | Parity, contradiction, descent |
| infinitude-of-primes | Prime factorization | Fundamental theorem of arithmetic |

## Initial Thoughts

### Potential Approaches

1. **Rational Root Theorem**: If p/q is a rational root of x³ - 2 = 0, then p divides 2 and q divides 1. Check all candidates: ±1, ±2. None cube to 2.

2. **Prime Multiplicity**: If (p/q)³ = 2, then 3·v₂(p) - 3·v₂(q) = 1, where v₂ is the 2-adic valuation. But LHS is divisible by 3, RHS is 1. Contradiction.

3. **Eisenstein's Criterion**: x³ - 2 is irreducible over ℚ by Eisenstein with p=2. Therefore it has no rational roots.

### Key Difficulties

- Parity argument fails (key insight!)
- Need to use divisibility/valuation or polynomial irreducibility
- Mathlib formalization of cube roots

### What Would a Proof Need?

- Mathlib: `Irrational`, `Polynomial.Irreducible`, or valuation theory
- Key lemma: one of the three approaches above

## Tractability Assessment

**Difficulty**: Challenging (but doable)

**Justification**:
- Well-known classical result with multiple proof strategies
- Mathlib has the Rational Root Theorem
- Similar to existing irrationality proofs in structure

**Estimated Effort**:
- Exploration: 2-4 hours
- Formalization (if tractable): 4-8 hours

## References

### Mathlib
- `Mathlib.Data.Real.Irrational` — Irrational number definitions
- `Mathlib.RingTheory.Polynomial.RationalRoot` — Rational root theorem
- `Mathlib.RingTheory.Polynomial.Eisenstein.Basic` — Eisenstein criterion

### Mathematical Background
- The rational root theorem: if p/q is a root of aₙxⁿ + ... + a₀, then p|a₀ and q|aₙ
- For x³ - 2 = 0: candidates are ±1, ±2, none of which work

## Metadata

```yaml
tags:
  - number-theory
  - irrationality
  - polynomial
  - algebraic-number-theory
related_proofs:
  - sqrt2-irrational
difficulty: challenging
source: proof-suggestion
created: 2024-12-30
```
