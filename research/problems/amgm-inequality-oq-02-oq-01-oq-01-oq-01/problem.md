# Problem: Specialize the general recurrence to concrete small k (k = 2, 3, 4) by evalua...

**Slug**: amgm-inequality-oq-02-oq-01-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
p_2 = e_1^2 - 2e_2,\quad p_3 = e_1^3 - 3e_1 e_2 + 3e_3,\quad p_4 = e_1^4 - 4e_1^2 e_2 + 2e_2^2 + 4e_1 e_3 - 4e_4
$$

### Plain Language

Specialize the parent's general Newton–Girard recurrence (relating power sums p_k to elementary symmetric polynomials e_k) to the concrete small cases k = 2, 3, 4 by evaluating the filtered antidiagonal sums, recovering the textbook closed-form identities.

### Why This Matters

The small-k Newton–Girard identities are the workhorses behind symmetric-function manipulations, Vieta-based root-sum computations, and trace/characteristic-polynomial formulas. Deriving them as instances of the parent's uniform recurrence both validates the general theorem and produces reusable named lemmas.

## Known Results

### What's Already Proven

- Parent `amgm-inequality-oq-02-oq-01-oq-01` proves the general Newton–Girard recurrence p_k = Σ (-1)^{i-1} e_i p_{k-i} + (-1)^{k-1} k e_k.
- Mathlib: `MvPolynomial.psum`, `MvPolynomial.esymm`, `MvPolynomial.psum_eq_sum_esymm` (Newton's identities).

### What's Still Open

This specific leaf — extracted as an open question from the parent proof `amgm-inequality-oq-02-oq-01-oq-01` — has not yet been formalized in the gallery.

### Our Goal

Instantiate the parent recurrence at k=2,3,4 and prove the explicit closed forms p_2, p_3, p_4 in terms of e_1..e_4.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `amgm-inequality-oq-02-oq-01-oq-01` | parent: general Newton–Girard recurrence | symmetric polynomials |
| `amgm-inequality` | AM-GM via symmetric functions | inequalities |

## Initial Thoughts

### Potential Approaches

1. **Reuse parent machinery**: The parent `amgm-inequality-oq-02-oq-01-oq-01` is verified (0-axiom); specialize / instantiate its main results to this leaf rather than re-deriving from scratch.
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
- `Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities` — Newton's identities.
- `MvPolynomial.psum`, `MvPolynomial.esymm`.

## Metadata

```yaml
tags:
  - algebra
  - symmetric-polynomials
  - newton-girard
  - power-sums
  - research
related_proofs:
  - amgm-inequality-oq-02-oq-01-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
