# Problem: Generating Function of the Catalan Numbers C(x) = (1−√(1−4x))/(2x)

**Slug**: combinations-formula-oq-02-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\text{For the Catalan numbers } C_n=\frac{1}{n+1}\binom{2n}{n},\ \text{the OGF } C(x)=\sum_{n\ge 0}C_n x^{n}\ \text{satisfies}\ x\,C(x)^2 - C(x) + 1 = 0,\ \text{hence}\ C(x)=\frac{1-\sqrt{1-4x}}{2x}.
$$

### Plain Language

The Catalan numbers C_n = (1/(n+1))·binom(2n,n) count binary trees, balanced parentheses, triangulations, etc. Their ordinary generating function C(x) = Σ C_n xⁿ satisfies the quadratic functional equation x·C(x)² − C(x) + 1 = 0 (from the convolution recurrence C_{n+1} = Σ C_i C_{n−i}), whose root is C(x) = (1−√(1−4x))/(2x). The goal is to formalize this generating-function identity — most robustly as the formal-power-series statement that the Catalan series satisfies the quadratic, and/or that the coefficients of (1−√(1−4x))/(2x) are the Catalan numbers.

### Why This Matters

- The Catalan generating function is one of the most-cited results in enumerative combinatorics, the canonical example of solving a recurrence via generating functions.
- It links the convolution recurrence C_{n+1}=Σ C_i C_{n−i} to a closed analytic form, and underlies the asymptotic C_n ∼ 4ⁿ/(n^{3/2}√π).
- Mathlib has PowerSeries, Catalan numbers (Nat.catalan / Catalan), and the convolution recurrence; the algebraic (quadratic functional equation) form avoids needing a formal square root.

## Known Results

### What's Already Proven

- Parent combinations-formula-oq-02 (verified, 0-axiom): central binomial / combinatorial identities feeding the Catalan recurrence.
- Mathlib: Catalan numbers and the convolution recurrence catalan_succ : catalan (n+1) = Σ_{i} catalan i * catalan (n-i).
- Mathlib: PowerSeries ring structure, PowerSeries.coeff, mul/coeff_mul (Cauchy product).

### What's Still Open

- Q1 (recommended, algebraic): Let C : PowerSeries ℚ be the Catalan OGF (coeff n C = catalan n). Prove the functional equation X * C^2 - C + 1 = 0 in PowerSeries ℚ, directly from the convolution recurrence via coeff_mul.
- Q2: Interpret the closed form: show C is the (unique, constant-term-1) power-series solution of x y² − y + 1 = 0, equivalently 2x·C = 1 − √(1−4x) as a formal-power-series square-root identity (1−2xC)² = 1−4x.
- Q3 (stretch): connect to the analytic radius 1/4 and the asymptotic C_n ∼ 4ⁿ n^{-3/2}/√π.

### Our Goal

Formalize that the Catalan generating function satisfies x·C(x)²−C(x)+1=0 (hence C(x)=(1−√(1−4x))/(2x)), proving the quadratic functional equation from the convolution recurrence in PowerSeries ℚ.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| combinations-formula-oq-02 | parent open question | source of this extension |
| combinations-formula | ancestor in the same family | shared definitions and lemmas |

## Initial Thoughts

### Potential Approaches

1. **Functional equation in PowerSeries (recommended)**: Define C with coeff n C = catalan n; compute coeff n (X*C^2) via PowerSeries.coeff_mul twice and match catalan_succ; conclude X*C^2 = C - 1 coefficientwise.
   - Risk: Index shifting between coeff (n) of X*C^2 and the (n-1) convolution; the constant term (n=0) base case.
2. **Square-root form via (1−2xC)²=1−4x**: From the quadratic, square 1−2xC and verify it equals the series 1−4x coefficientwise, giving the (1−√(1−4x))/(2x) closed form without a primitive sqrt operation.
   - Risk: Mathlib's formal square root for power series is limited; the squared identity sidesteps it but the 'extract the minus root' step needs the constant-term argument.

### Key Difficulties

- Mathlib lacks a ready formal power-series square root, so the literal (1−√(1−4x))/(2x) must be encoded as the quadratic functional equation / squared identity.
- Coefficient index bookkeeping in X*C² (the X shift) against catalan_succ.

### What Would a Proof Need?

- Catalan convolution recurrence (catalan_succ) in Mathlib.
- PowerSeries.coeff_mul (Cauchy product) and ring lemmas.
- Constant-term / base-case handling for the X-shift.

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- The combinatorics is classical and the recurrence is in Mathlib, but the generating-function/power-series plumbing makes it the hardest of this batch.
- Encoding the closed form as the quadratic functional equation keeps it within Mathlib's PowerSeries API and avoids the missing formal sqrt.
- Sibling combinations-formula OQ entries have been formalized, so the surrounding infrastructure is proven usable.

**Estimated Effort**:
- Exploration: hours
- If tractable: days

## References

### Papers
- R. P. Stanley, Enumerative Combinatorics Vol. 2 (1999) Ch. 6 + Catalan addendum.
- P. Flajolet, R. Sedgewick, Analytic Combinatorics (2009) §I.5 — Catalan GF.

### Online Resources
- https://en.wikipedia.org/wiki/Catalan_number#Generating_function
- https://oeis.org/A000108

### Mathlib
- Mathlib.Combinatorics.Catalan — Catalan numbers, catalan_succ recurrence
- Mathlib.RingTheory.PowerSeries.Basic — PowerSeries, coeff, coeff_mul
- Mathlib.RingTheory.PowerSeries.WellKnown — known series identities

## Metadata

```yaml
tags:
  - seeker-selected
  - combinatorics
  - catalan-numbers
  - generating-functions
  - power-series
  - binomial-coefficients
  - central-binomial
related_proofs:
  - combinations-formula
  - combinations-formula-oq-02
difficulty: medium
source: proof-suggestion
created: 2026-06-24
```
