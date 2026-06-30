# Problem: Falling-Factorial Second Moment of Squared Binomials

**Slug**: combinations-formula-oq-07-oq-04-oq-02
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent computes the second moment $\sum_{k} k^2 \binom{n}{k}^2$ of the squares
of binomial coefficients. This leaf asks for the **falling-factorial** second
moment, which has a cleaner single-term closed form via double absorption:

$$
\sum_{k=0}^{n} k(k-1)\binom{n}{k}^2 \;=\; n(n-1)\binom{2n-2}{\,n-2\,}.
$$

The key step is iterating the absorption identity $k\binom{n}{k} = n\binom{n-1}{k-1}$
twice, giving $k(k-1)\binom{n}{k}^2 = n(n-1)\binom{n-2}{k-2}\binom{n}{k}$, then
applying Vandermonde to the resulting convolution. The falling-factorial form yields
the variance of the hypergeometric-type distribution directly, without recombining
raw moments. Prove it in Lean 4.

### Plain Language

The parent measures the "spread" of squared binomial coefficients using $k^2$. Using
the falling factorial $k(k-1)$ instead makes the algebra telescope: two applications
of the absorption rule collapse the whole sum to a single central binomial
coefficient $n(n-1)\binom{2n-2}{n-2}$. This is the natural quantity for reading off
the variance.

### Why This Matters

Shows that the right basis for binomial-coefficient moments is the falling factorial,
not ordinary powers — a standard but instructive simplification, and a clean Lean
exercise in the absorption + Vandermonde toolkit.

## Known Results

### What's Already Proven

- `combinations-formula-oq-07-oq-04` (verified) — second moment $\sum k^2 \binom{n}{k}^2$.
- Mathlib: `Nat.succ_mul_choose_eq` (absorption), Vandermonde / `Nat.add_choose_le` API.

### What's Still Open

- The falling-factorial closed form (this problem).

### Our Goal

Prove $\sum_{k} k(k-1)\binom{n}{k}^2 = n(n-1)\binom{2n-2}{n-2}$ by double absorption
+ Vandermonde, then optionally derive the variance.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| combinations-formula-oq-07-oq-04 | direct parent | second moment, absorption |
| vandermonde-interpolation-oq-01 | Vandermonde convolution | binomial convolution |

## Initial Thoughts

### Potential Approaches

1. **Double absorption then Vandermonde**: rewrite the summand and reindex.
   - Why it might work: each absorption is a Mathlib one-liner; Vandermonde is in Mathlib.
   - Risk: index-shift bookkeeping ($k-2$ shift, boundary terms $k<2$ vanish).

### Key Difficulties

- Handling the $k = 0, 1$ boundary terms (they vanish under $k(k-1)$) cleanly.
- Matching Mathlib's Vandermonde statement to the shifted convolution.

### What Would a Proof Need?

- Absorption applied twice to $k(k-1)\binom{n}{k}$.
- Vandermonde / Cauchy convolution for central binomial.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Pure `Nat.choose` algebra; parent already navigated the squared-binomial moment.
- Main cost is reindexing discipline, not new mathematics.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days

## References

### Mathlib
- `Mathlib.Combinatorics.Choose.*` — absorption, Vandermonde.

## Metadata

```yaml
tags:
  - combinatorics
  - binomial-coefficients
related_proofs:
  - combinations-formula-oq-07-oq-04
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
