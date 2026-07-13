# Problem: Cauchy-Schwarz for Complex Inner Product Spaces

**Slug**: cauchy-schwarz-oq-01
**Created**: 2026-02-23T22:06:16-08:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a complex inner product space $(H, \langle \cdot, \cdot \rangle)$, the Cauchy-Schwarz inequality states:

$$
|\langle x, y \rangle| \leq \|x\| \cdot \|y\| \quad \text{for all } x, y \in H
$$

The goal is to extend the existing `cauchy-schwarz` Lean formalization to work over complex inner product spaces using Mathlib's `inner_mul_le_norm_mul_norm`.

### Plain Language

The existing gallery proof of Cauchy-Schwarz works over real inner product spaces. Complex inner product spaces require handling conjugate-linearity and the modulus of complex numbers. The question is: can we use Mathlib's `inner_mul_le_norm_mul_norm` (which already supports complex inner products) to complete this extension and formalize the complex case cleanly?

### Why This Matters

Cauchy-Schwarz over complex spaces is foundational for:
- Quantum mechanics (Hilbert space formalism)
- Functional analysis (bounded operators)
- Complex Fourier analysis
- L² spaces over complex-valued functions

## Known Results

### What's Already Proven

- Real Cauchy-Schwarz in Lean gallery (`cauchy-schwarz`)
- `inner_mul_le_norm_mul_norm` in Mathlib (works for complex inner products)
- `abs_inner_le_norm` in Mathlib.Analysis.InnerProductSpace.Basic
- Complex inner product spaces formalized via `InnerProductSpace ℂ E`

### What's Still Open

- Gallery proof explicitly extended to complex case
- Verification that `inner_mul_le_norm_mul_norm` subsumes the real case
- Clean formalization showing both real and complex cases as instances

### Our Goal

Extend or generalize the `cauchy-schwarz` gallery entry to formally verify the complex inner product space case using Mathlib primitives. Either:
1. Show the existing proof works uniformly over `𝕜` (ℝ or ℂ), or
2. Create a companion proof `cauchy-schwarz-complex.lean` demonstrating the complex case

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cauchy-schwarz | Direct predecessor — real case | norm_nonneg, inner_self_eq_norm_sq |
| cauchy-schwarz-integral | Integral variant — same inequality | MeasureTheory.inner_mul_le_norm |
| amgm-inequality | Related classical inequality | algebraic manipulation |

## Initial Thoughts

### Potential Approaches

1. **Uniform approach over `𝕜`**: Make the existing proof polymorphic over `𝕜 = ℝ` or `𝕜 = ℂ`
   - Why it might work: Mathlib's `InnerProductSpace` is already parameterized by a field `𝕜`
   - Risk: The proof may rely on `ℝ`-specific properties (no modulus needed)

2. **Direct use of Mathlib**: Simply state `theorem` using `inner_mul_le_norm_mul_norm` or `abs_inner_le_norm`
   - Why it might work: These are already in Mathlib, so the proof may be `exact abs_inner_le_norm x y`
   - Risk: May be too trivial — need to add value beyond just re-stating Mathlib

3. **New companion file with complex-specific content**: Show applications unique to complex spaces (polarization identity, etc.)
   - Why it might work: Adds genuine new mathematical content
   - Risk: Scope creep

### Key Difficulties

- Complex inner products are conjugate-linear in first argument (or second, depending on convention)
- Mathlib uses `RCLike` typeclass to unify ℝ and ℂ cases
- Need to decide if the goal is formalization or just using existing Mathlib lemmas

### What Would a Proof Need?

- Import `Mathlib.Analysis.InnerProductSpace.Basic`
- Instance `InnerProductSpace ℂ E` for some type `E`
- The key lemma: `inner_mul_le_norm_mul_norm : ‖⟪x, y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖`

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- `inner_mul_le_norm_mul_norm` already exists in Mathlib — the proof may be trivial
- The interesting work is building a meaningful formalization around it
- Similar to how `cauchy-schwarz` formalizes what Mathlib already knows

**Estimated Effort**:
- Exploration: 1-2 hours (locate relevant Mathlib APIs)
- If tractable: 1-3 days (write clean formalization with applications)

## References

### Mathlib
- `Mathlib.Analysis.InnerProductSpace.Basic` — `inner_mul_le_norm_mul_norm`, `abs_inner_le_norm`
- `Mathlib.Analysis.RCLike.Basic` — `RCLike` typeclass unifying ℝ and ℂ
- `Mathlib.Analysis.InnerProductSpace.PiL2` — product inner product spaces

### Online Resources
- Mathlib4 docs: `InnerProductSpace` — complex inner product space class

## Metadata

```yaml
tags:
  - analysis
  - linear-algebra
  - inner-product-spaces
  - complex-analysis
  - functional-analysis
  - classic
related_proofs:
  - cauchy-schwarz
  - cauchy-schwarz-integral
difficulty: low-medium
source: gallery-gap
created: 2026-02-23T22:06:16-08:00
```

**Significance**: 8/10
**Tractability**: 7/10
