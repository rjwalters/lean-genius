# Problem: Vieta — Sum and Product of Roots of a Monic Split Polynomial

**Slug**: vietas-formulas-oq-05
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: vietas-formulas

## Problem Statement

### Formal Statement

For a monic polynomial `p` over a field `K` that **splits** over `K`,

$$
\prod_{r \in \text{roots}(p)} r = (-1)^{\deg p}\, p_0,
\qquad
\sum_{r \in \text{roots}(p)} r = -\,[\text{next coefficient of } p],
$$

where `p_0 = p.coeff 0` and the *next coefficient* is the coefficient of `X^{deg p - 1}`.

### Plain Language

The parent `vietas-formulas` states Vieta's relations. This child pins down the two
headline cases as clean, reusable lemmas over `Polynomial.roots`: the **product of all roots
(with multiplicity)** equals `(-1)^n` times the constant term, and the **sum of all roots**
equals the negative of the `X^{n-1}` coefficient — for any monic split polynomial, in one
statement, with a fully worked cubic.

### Why This Matters

Mathlib's current API states these through `Polynomial.Splits.coeff_zero_eq_prod_roots_of_monic`
and `Polynomial.Splits.nextCoeff_eq_neg_sum_roots_of_monic` (the older
`prod_roots_eq_coeff_zero_of_monic_of_splits` spellings are now deprecated). This child gives
the *root-side* orientation (`roots.prod = …`, `roots.sum = …`) that matches how Vieta is
taught and used, and demonstrates it on a concrete cubic — a small but genuinely useful
curated packaging on top of a recently-renamed API.

## Known Results

### What's Already Proven

- Parent `vietas-formulas` is verified (0-axiom).
- Mathlib (current, non-deprecated):
  `Polynomial.Splits.coeff_zero_eq_prod_roots_of_monic (hf : Splits f) (hm : Monic f) :
   coeff f 0 = (-1) ^ f.natDegree * f.roots.prod`;
  `Polynomial.Splits.nextCoeff_eq_neg_sum_roots_of_monic (hf : Splits f) (hm : Monic f) :
   f.nextCoeff = -f.roots.sum`;
  `Polynomial.Splits.eq_prod_roots_of_monic`.

### What's Still Open

- The root-oriented restatements and the worked cubic below (currently `sorry`).

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**restatement / worked corollary**.

## Target Lean Sketch

```lean
open Polynomial

variable {K : Type*} [Field K] {p : K[X]}

/-- Product of the roots of a monic split polynomial. -/
theorem prod_roots_of_monic (hm : p.Monic) (hsp : p.Splits (RingHom.id K)) :
    p.roots.prod = (-1) ^ p.natDegree * p.coeff 0 := by
  -- from `Splits.coeff_zero_eq_prod_roots_of_monic`: coeff 0 = (-1)^n * roots.prod;
  -- multiply both sides by (-1)^n and use `(-1)^n * (-1)^n = 1`.
  sorry

/-- Sum of the roots of a monic split polynomial. -/
theorem sum_roots_of_monic (hm : p.Monic) (hsp : p.Splits (RingHom.id K)) :
    p.roots.sum = - p.nextCoeff := by
  -- immediate from `Splits.nextCoeff_eq_neg_sum_roots_of_monic` + `neg_neg`.
  sorry
```

Add a fully worked `example` over `ℝ` or `ℂ`: `p = (X - 1) * (X - 2) * (X - 3)
= X^3 - 6 X^2 + 11 X - 6`, verifying `roots.sum = 6 = -(-6)` and
`roots.prod = 6 = (-1)^3 * (-6)`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `vietas-formulas` | Parent: Vieta's relations | symmetric functions, roots |
| `fundamental-theorem-algebra` | Splitting over `ℂ` guarantees roots | complex analysis |
| `solution-of-cubic` | Concrete cubic root relations | Cardano |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 5/10  |  **Tractability**: 9/10  |  **Tier**: B

**Justification**: Both statements are short rearrangements of existing (current, un-deprecated)
Mathlib lemmas; the sign bookkeeping `(-1)^n * (-1)^n = 1` and `neg_neg` is routine. The worked
cubic is `norm_num`/`decide`-friendly after computing `roots`.

### Suggested First Steps

1. Prove `sum_roots_of_monic` directly from `Splits.nextCoeff_eq_neg_sum_roots_of_monic`.
2. Prove `prod_roots_of_monic` by isolating `roots.prod` in
   `Splits.coeff_zero_eq_prod_roots_of_monic` (multiply by `(-1)^n`, simplify with `Even`/`pow`
   lemmas).
3. Build the worked cubic: compute `roots` of `(X-1)(X-2)(X-3)` and check both relations.

## References

### Mathlib

- `Polynomial.Splits.coeff_zero_eq_prod_roots_of_monic` — Algebra/Polynomial/Factors.lean
- `Polynomial.Splits.nextCoeff_eq_neg_sum_roots_of_monic` — Algebra/Polynomial/Factors.lean
- `Polynomial.Splits.eq_prod_roots_of_monic` — Algebra/Polynomial/Factors.lean

### Literature

- Vieta's formulas relating coefficients to elementary symmetric functions of the roots.

## Metadata

```yaml
tags:
  - algebra
  - polynomials
  - vietas-formulas
  - roots
related_proofs:
  - vietas-formulas
  - fundamental-theorem-algebra
  - solution-of-cubic
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
