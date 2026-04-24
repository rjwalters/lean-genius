# Problem: Remove Change-of-Variables Axioms via MeasureTheory

**Slug**: area-of-circle-oq-01-oq-03-oq-01-oq-03
**Created**: 2026-04-24T10:35:16+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The source proof `area-of-circle-oq-01-oq-03-oq-01` (Arc-Length Reparametrization for
Smooth Closed Curves) uses axiom declarations for change-of-variables steps in the
circumference integral. Replace these with the Mathlib lemma:

```lean
MeasureTheory.integral_image_eq_integral_abs_deriv_smul
```

### Plain Language

The isoperimetric inequality proof chain includes a sub-proof about arc-length
reparametrization for smooth closed curves. That sub-proof relies on `axiom`
declarations for change-of-variables steps in integrals. The task is to eliminate
these axioms using Mathlib's measure-theory infrastructure, specifically
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul`, which handles the
change-of-variables formula for the circumference integral.

### Why This Matters

Eliminating axioms from the proof chain improves the mathematical soundness of the
isoperimetric inequality formalization. Each removed axiom moves the proof toward
`status: verified` (0 axioms, 0 sorries). This continues the pattern established by
the LP duality synthesis.

## Known Results

### What's Already Proven

- `area-of-circle-oq-01-oq-03-oq-01`: Arc-length reparametrization for smooth closed
  curves — exists but uses axioms for change-of-variables steps
- `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` — exists in Mathlib 4,
  handles measure-preserving change of variables with absolute derivative

### What's Still Open

- Whether the Mathlib lemma's hypotheses (injectivity, differentiability) can be
  discharged for the arc-length reparametrization case
- Whether auxiliary lemmas about arc-length are in Mathlib or need to be proved

### Our Goal

Replace the change-of-variables axiom declarations in the source proof with formal
proofs using `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| area-of-circle-oq-01-oq-03-oq-01 | Direct source — contains axioms to eliminate | Arc-length, reparametrization |
| area-of-circle-oq-01 | Top-level isoperimetric inequality | Integration, Fourier |
| cauchy-schwarz-integral-lp-duality-synthesis | Same pattern: axiom elimination via Mathlib | Lp duality, measure theory |

## Initial Thoughts

### Potential Approaches

1. **Direct application of `integral_image_eq_integral_abs_deriv_smul`**:
   - Show arc-length reparametrization φ is C¹ and injective
   - Apply the lemma to transform the circumference integral
   - Why it might work: lemma exists and matches mathematical content
   - Risk: may need to establish injectivity and |φ'| ≠ 0

2. **Use IFT for the inverse arc-length map**:
   - Arc-length s(t) is strictly increasing when |γ'| > 0
   - Inverse s⁻¹ is C¹ by the inverse function theorem
   - Then apply change-of-variables to the circumference integral
   - Risk: IFT in Mathlib may require careful hypothesis matching

### Key Difficulties

- Arc-length reparametrization injectivity: need φ'(t) ≠ 0 a.e.
- The `abs_deriv` condition: |φ'(t)| = 1/|γ'(φ(t))| for the inverse reparametrization
- Connecting smooth curve hypotheses to Mathlib's `HasDerivAt` framework

### What Would a Proof Need?

- Key lemma: arc-length function is C¹ with nonzero derivative (from |γ'| > 0)
- `HasDerivAt` for the arc-length reparametrization inverse
- Application of `integral_image_eq_integral_abs_deriv_smul` with computed Jacobian

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The target Mathlib lemma is identified exactly
- Mathematical argument is standard (IFT + change of variables)
- Same axiom-elimination pattern succeeded for LP duality synthesis
- Main challenge: navigating Mathlib's API for arc-length and smooth curves

**Estimated Effort**:
- Exploration: 1-2 days (find relevant Mathlib lemmas, understand the API)
- If tractable: 2-5 days (write proof connecting the pieces)
- If hard: may need auxiliary lemmas about arc-length not yet in Mathlib

## References

### Mathlib
- `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` — change of variables
- `ContDiff.hasStrictFDerivAt_of_hasStrictFDerivAt` — C¹ inverse
- `Real.hasStrictDerivAt_inv` — pointwise derivative of inverse
- `MeasureTheory` arc-length infrastructure (search `ArcLength`, `pathLength`)

## Metadata

```yaml
tags:
  - measure-theory
  - real-analysis
  - axiom-elimination
  - arc-length
  - reparametrization
  - isoperimetric
related_proofs:
  - area-of-circle-oq-01-oq-03-oq-01
  - area-of-circle-oq-01
  - cauchy-schwarz-integral-lp-duality-synthesis
difficulty: medium
source: gallery-gap
created: 2026-04-24T10:35:16+02:00
```
