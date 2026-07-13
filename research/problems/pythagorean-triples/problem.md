# Problem: Density of Primitive Pythagorean Triples

**Slug**: pythagorean-triples
**Created**: 2026-03-11
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
P(N) = \#\{(a,b,c) : a^2 + b^2 = c^2,\; \gcd(a,b)=1,\; a < b,\; c \leq N\} \sim \frac{N}{2\pi} \text{ as } N \to \infty
$$

### Plain Language

Count the number of primitive Pythagorean triples (a,b,c) with hypotenuse c at most N. This count grows like N/(2π). We want to formalize this asymptotic formula in Lean 4.

### Why This Matters

This connects the algebraic parametrization of Pythagorean triples (already in our gallery) to analytic number theory. The appearance of π in a counting problem about integers is a beautiful connection between discrete and continuous mathematics.

## Known Results

### What's Already Proven

- Parametrization: every primitive triple is (m²-n², 2mn, m²+n²) with m > n > 0, gcd(m,n)=1, m ≢ n (mod 2) — `pythagorean-triples` gallery proof
- Gauss circle problem: lattice points in circle of radius R ~ πR²

### What's Still Open

- Formal asymptotic P(N) ~ N/(2π) in Lean
- Error term analysis

### Our Goal

Prove P(N) ~ N/(2π) by counting coprime pairs (m,n) with m²+n² ≤ N, using the density of coprime pairs (6/π²) and quarter-circle area (π/4).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| pythagorean-triples | Direct parent — parametrization | gcd, parity |
| euler-totient | Coprime pair density | Euler's totient, Möbius |
| area-of-circle | Circle area formalization | Integration |

## Initial Thoughts

### Potential Approaches

1. **Lattice point counting**: Count (m,n) pairs with m²+n² ≤ N, coprime, opposite parity
   - Why it might work: Reduces to well-known estimates
   - Risk: Asymptotic formalization in Lean can be tricky

2. **Möbius inversion**: Use inclusion-exclusion on gcd condition
   - Why it might work: Systematic approach to coprimality constraints
   - Risk: Möbius function machinery needed

### Key Difficulties

- Formalizing "f(N) ~ g(N)" (asymptotic equivalence) in Lean
- Handling the coprimality and parity constraints simultaneously
- The factor 1/(2π) comes from (6/π²)·(π/4)·(1/2)·4 = 3/π — need careful tracking

### What Would a Proof Need?

- Key lemma 1: Density of coprime pairs: #{(m,n) ≤ R : gcd(m,n)=1} ~ 6R²/π²
- Key lemma 2: Quarter-circle lattice point count
- Key lemma 3: Parity constraint halves the count
- Technical requirements: Asymptotic analysis, Euler products

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- Parametrization already formalized
- Asymptotic estimates require analytic number theory machinery
- Mathlib has Euler totient but asymptotic density tools are limited

## References

### Papers
- Lehmer, "Asymptotic evaluation of certain totient sums"
- Hardy & Wright, "An Introduction to the Theory of Numbers", Ch. 20

### Mathlib
- `Mathlib.NumberTheory.ArithmeticFunction` — Euler totient, Möbius
- `Mathlib.Analysis.Asymptotics` — asymptotic notation

## Metadata

```yaml
tags:
  - number-theory
  - asymptotics
  - counting
  - pythagorean-triples
related_proofs:
  - pythagorean-triples
  - euler-totient
  - area-of-circle
difficulty: medium-high
source: gallery-gap
created: 2026-03-11
```
