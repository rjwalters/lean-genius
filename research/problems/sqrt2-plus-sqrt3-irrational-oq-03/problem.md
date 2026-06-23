# Problem: Minimal Polynomial of √2+√3 over ℚ

**Slug**: sqrt2-plus-sqrt3-irrational-oq-03
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
f(x) = x^4 - 10x^2 + 1 \text{ satisfies } f(\sqrt{2}+\sqrt{3}) = 0 \text{ and } f \text{ is irreducible over } \mathbb{Q}
$$

Equivalently: $[\mathbb{Q}(\sqrt{2}+\sqrt{3}) : \mathbb{Q}] = 4$.

### Plain Language

The gallery has already proved √2+√3 is irrational. This problem asks us to go further: compute the *minimal polynomial* of α = √2+√3 over ℚ, which is the unique monic irreducible polynomial with rational coefficients that has α as a root.

The polynomial is f(x) = x⁴ - 10x² + 1. We need to:
1. Show f(α) = 0 by direct computation: (√2+√3)² = 5+2√6, so (√2+√3)⁴ = 49+20√6, giving f(α) = 49+20√6 - 50 - 20√6 + 1 = 0. ✓
2. Prove f is irreducible over ℚ (no rational roots via rational root theorem; no factorization into quadratics by checking all possibilities).

### Why This Matters

The minimal polynomial is a fundamental algebraic invariant. This result:
- Establishes [ℚ(√2+√3):ℚ] = 4, proving it's a degree-4 extension
- Shows {1, √2, √3, √6} is a basis for ℚ(√2+√3) over ℚ (used in Besicovitch's theorem)
- Demonstrates the Eisenstein-like approach to irreducibility
- Is a concrete, fully computable formalization target

## Known Results

### What's Already Proven

- `sqrt2-plus-sqrt3-irrational`: √2+√3 is irrational (in gallery)
- Rational root theorem: only ±1 are candidate rational roots (both fail for f)
- In Mathlib: `Polynomial.Irreducible`, `Polynomial.isUnit_or_isUnit_of_associated`

### What's Still Open

- Formal Lean proof that x⁴ - 10x² + 1 has no rational roots (follows from rational root theorem check)
- Formal Lean proof of irreducibility over ℚ (no quadratic factorization)

### Our Goal

Prove: `theorem sqrt2_add_sqrt3_minpoly : Polynomial.minpoly ℚ (Real.sqrt 2 + Real.sqrt 3) = X^4 - C 10 * X^2 + 1`

or equivalently show the polynomial is irreducible and vanishes at √2+√3.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sqrt2-plus-sqrt3-irrational | Direct predecessor | Irrationality via squaring |
| algebraic-numbers-countable | Context | Algebraic numbers are countable |
| cube-root-2-irrational | Similar structure | Minimal polynomial of ∛2 is x³-2 |

## Initial Thoughts

### Potential Approaches

1. **Direct computation + rational root theorem + quadratic factor elimination**
   - Compute f(√2+√3) = 0 explicitly in Lean: (√2+√3)^4 - 10(√2+√3)^2 + 1
   - Rational root theorem: rational roots of x⁴-10x²+1 would be ±1, check both fail
   - For quadratic factors: assume f = (x²+ax+b)(x²-ax+c) over ℚ, derive contradiction
   - Why it might work: fully elementary, no advanced theory needed
   - Risk: tedious but doable

2. **Via Mathlib's `minpoly` API**
   - Use `minpoly.eq_X_pow_sub_C_of_isSplittingField` or similar
   - Show f is monic, has √2+√3 as root, and is irreducible
   - Why it might work: Mathlib has strong minimal polynomial infrastructure
   - Risk: may need field theory setup (ℚ-algebra structure on ℝ)

### Key Difficulties

- Setting up the ℚ-algebra structure on ℝ to use `minpoly`
- Proving irreducibility: quadratic factorization case requires solving a system of equations over ℚ

### What Would a Proof Need?

- `Real.sqrt_mul`, `Real.sq_sqrt` for computation
- `Polynomial.eval_add`, `Polynomial.eval_pow` for evaluation
- `Polynomial.Irreducible` or `Irreducible` instance for ℤ[x] → ℚ[x]

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- The minimal polynomial is known explicitly (x⁴ - 10x² + 1)
- Verifying f(√2+√3) = 0 is a direct computation (30 lines of Lean)
- Irreducibility is an elementary check (no rational roots + no quadratic factors)
- All required Mathlib lemmas exist
- Similar to `sqrt2-irrational` and `cube-root-2-irrational` in structure

**Estimated Effort**:
- Exploration: 1-2 hours
- Implementation: 2-4 hours
- Total: tractable in a single session

## References

### Papers
- Besicovitch, A.S. (1940). "On the linear independence of fractional powers of integers" — gives the general theory

### Mathlib
- `Mathlib.RingTheory.Polynomial.Basic` — polynomial ring over ℚ
- `Mathlib.NumberTheory.NumberField.Basic` — algebraic numbers
- `Mathlib.Algebra.Polynomial.Eval` — polynomial evaluation

## Metadata

```yaml
tags:
  - algebraic-number-theory
  - field-extensions
  - irreducibility
  - minimal-polynomial
  - seeker-selected
related_proofs:
  - sqrt2-plus-sqrt3-irrational
  - cube-root-2-irrational
  - algebraic-numbers-countable
difficulty: low
source: gallery-gap
created: 2026-04-21
```

**Significance**: 6/10
**Tractability**: 9/10
