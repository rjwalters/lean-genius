# Problem: Specialize the formula to the 2×2 and 3×3 cases, recovering the elementary cl...

**Slug**: cramers-rule-oq-04-oq-01-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
n=2:\ x_i=\frac{\det A_i}{\det A};\quad n=3:\ x_i=\frac{\det A_i}{\det A},\ \det A = a(ei-fh)-b(di-fg)+c(dh-eg)
$$

### Plain Language

Specialize the parent's general Cramer's-rule / cofactor-expansion formula to the explicit 2×2 and 3×3 cases, recovering the elementary classroom determinant and solution formulas as fully expanded named lemmas.

### Why This Matters

The 2×2 and 3×3 closed forms are the most-used instances of Cramer's rule and the Laplace expansion. Deriving them from the general theorem provides concrete, directly-applicable lemmas and validates the general formula against the textbook cases.

## Known Results

### What's Already Proven

- Parent `cramers-rule-oq-04-oq-01-oq-01` establishes the general Cramer's rule via the adjugate (`Matrix.cramer`, `Matrix.adjugate`, `Matrix.mulVec_cramer`).
- Mathlib: `Matrix.det_fin_two`, `Matrix.det_fin_three`, `Matrix.cramer`.

### What's Still Open

This specific leaf — extracted as an open question from the parent proof `cramers-rule-oq-04-oq-01-oq-01` — has not yet been formalized in the gallery.

### Our Goal

Prove the fully expanded 2×2 and 3×3 Cramer solution formulas as instances of the parent's general result.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `cramers-rule-oq-04-oq-01-oq-01` | parent: general Cramer's rule via adjugate | determinants, adjugate |
| `cramers-rule` | Cramer's rule | linear systems |

## Initial Thoughts

### Potential Approaches

1. **Reuse parent machinery**: The parent `cramers-rule-oq-04-oq-01-oq-01` is verified (0-axiom); specialize / instantiate its main results to this leaf rather than re-deriving from scratch.
2. **Lean directly on Mathlib**: Several of the required notions already exist in Mathlib (see References); the work is connecting them to the parent's statement.

### What Would a Proof Need?

- Import and apply the parent proof's verified lemmas.
- Bridge lemmas connecting the parent's formulation to standard Mathlib definitions.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Direct extension of a verified, 0-axiom parent proof.
- Required supporting definitions exist in Mathlib.
- Clear first step: instantiate / specialize the parent result.

## References

### Mathlib
- `Mathlib.LinearAlgebra.Matrix.Adjugate` — `Matrix.cramer`, `Matrix.mulVec_cramer`.
- `Matrix.det_fin_two`, `Matrix.det_fin_three`.

## Metadata

```yaml
tags:
  - linear-algebra
  - cramers-rule
  - determinants
  - research
related_proofs:
  - cramers-rule-oq-04-oq-01-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
