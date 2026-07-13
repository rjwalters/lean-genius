# Problem: q-Vandermonde Identity via q-Binomial Antidiagonal Reindexing

**Slug**: combinations-formula-oq-07-oq-02
**Created**: 2026-07-02T01:25:36-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\binom{m+n}{k}_q = \sum_{i=0}^{k} q^{(m-i)(k-i)} \binom{m}{i}_q \binom{n}{k-i}_q ,
$$
the $q$-analogue of Vandermonde's convolution, where $\binom{a}{b}_q$ is the Gaussian binomial
coefficient.

### Plain Language

The classical Vandermonde convolution $\binom{m+n}{k} = \sum_i \binom{m}{i}\binom{n}{k-i}$ has a
$q$-deformed version: replacing ordinary binomials by Gaussian ($q$-)binomials introduces a power of
$q$ weight $q^{(m-i)(k-i)}$ in each term. We want to prove this $q$-Vandermonde identity in Lean,
mirroring the antidiagonal-to-range reindexing used for the ordinary case in the parent proof.

### Why This Matters

The $q$-Vandermonde identity is the combinatorial backbone of $q$-series and Gaussian-binomial
manipulation: it specializes to ordinary Vandermonde at $q=1$ and underlies $q$-hypergeometric
summation. Establishing it in the gallery closes the loop opened by the $q$-binomial theorem
(combinations-formula-oq-03) and by the ordinary Vandermonde convolution (parent oq-07), showing the
same reindexing engine transfers to the $q$-graded setting.

## Known Results

### What's Already Proven

- Ordinary Vandermonde convolution and the central-binomial sum of squares — parent `combinations-formula-oq-07` (verified).
- Gauss $q$-binomial theorem $\prod_{i=0}^{n-1}(1+q^i x) = \sum_k q^{\binom{k}{2}} \binom{n}{k}_q x^k$ — `combinations-formula-oq-03-oq-02` (verified).
- Mathlib `Nat.choose`, `Finset.Nat.antidiagonal`, and `Polynomial.Gaussian`-style $q$-binomial API where present.

### What's Still Open

- The $q$-Vandermonde convolution itself in Lean.
- Confirming the $q^{(m-i)(k-i)}$ weight normalization (conventions vary) and its $q=1$ collapse to ordinary Vandermonde.

### Our Goal

Prove $\binom{m+n}{k}_q = \sum_{i} q^{(m-i)(k-i)} \binom{m}{i}_q \binom{n}{k-i}_q$ by extracting the
coefficient of $x^k$ in the factorization $\prod_{j=0}^{m+n-1}(1+q^j x) = \big(\prod_{j<m}(1+q^j x)\big)\big(\prod_{j<n}(1+q^{m+j} x)\big)$
and matching it, via the $q$-binomial theorem, against the antidiagonal sum — exactly the strategy
the parent used at $q=1$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| combinations-formula-oq-07 | Direct parent: ordinary Vandermonde via antidiagonal reindexing | coefficient extraction, `antidiagonal` |
| combinations-formula-oq-03-oq-02 | Supplies the Gauss $q$-binomial theorem infrastructure | $q$-binomial coefficient, product-to-sum |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Coefficient extraction from the split product.
   - Why it might work: $\prod_{j=0}^{m+n-1}(1+q^j x)$ factors as a product over $[0,m)$ and $[m,m+n)$; applying the $q$-binomial theorem to each factor and to the whole, then equating coefficients of $x^k$, yields the identity with the correct $q$-weight from the shift $q^{m+j}$.
   - Risk: tracking the $q^{\binom{k}{2}}$ normalizations so the cross-term weight simplifies to $q^{(m-i)(k-i)}$.

2. **Approach B**: Induction on $n$ using the $q$-Pascal rule $\binom{a}{b}_q = \binom{a-1}{b-1}_q + q^b \binom{a-1}{b}_q$.
   - Why it might work: reduces $q$-Vandermonde to a one-step recurrence.
   - Risk: bookkeeping of $q$-powers across the induction is error-prone.

### Key Difficulties

- Normalization conventions for Gaussian binomials in Mathlib vs. the $q^{\binom{k}{2}}$-weighted form of the $q$-binomial theorem used in oq-03.
- Making the cross-weight $q^{(m-i)(k-i)}$ fall out cleanly after coefficient extraction.

### What Would a Proof Need?

- Key lemma 1: $q$-binomial theorem for a shifted product $\prod_{j=0}^{n-1}(1+q^{c+j}x)$.
- Key lemma 2: coefficient-of-$x^k$ in a product = antidiagonal convolution of coefficients.
- Technical requirements: Gaussian-binomial API, `Polynomial.coeff_mul`, `Finset.antidiagonal`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- [Reason for assessment] Both required tools (ordinary Vandermonde reindexing, Gauss $q$-binomial theorem) already exist verified in the gallery; the work is combining them with correct $q$-weight tracking.
- [Similar problems that have been solved] Parent oq-07 and the $q$-binomial oq-03-oq-02 are directly reusable engines.
- [Techniques available in Mathlib] `Polynomial.coeff_mul`, `Finset.Nat.antidiagonal`, Gaussian-binomial lemmas.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: 3–6 days
- If hard: unknown

## References

### Papers
- G. E. Andrews, "The Theory of Partitions" (1976) — $q$-Vandermonde and $q$-series foundations.

### Online Resources
- https://en.wikipedia.org/wiki/Gaussian_binomial_coefficient#q-Vandermonde_identity — statement and normalizations.

### Mathlib
- `Mathlib.Combinatorics.Choose.Vandermonde` — ordinary Vandermonde as a template; Gaussian-binomial support in `Mathlib.RingTheory` / gallery oq-03 file.

## Metadata

```yaml
tags:
  - combinatorics
  - q-analogue
  - q-binomial
related_proofs:
  - combinations-formula-oq-07
  - combinations-formula-oq-03-oq-02
difficulty: medium
source: gallery-gap
created: 2026-07-02T01:25:36-07:00
```

**Significance**: 5/10
**Tractability**: 6/10
