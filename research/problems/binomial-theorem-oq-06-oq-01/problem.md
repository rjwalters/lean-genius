# Problem: Alternating (Signed) Vandermonde Convolution

**Slug**: binomial-theorem-oq-06-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\sum_{k=0}^{r} (-1)^k \binom{m}{k}\binom{n}{r-k}
= [x^r]\,(1-x)^m (1+x)^n,
\qquad
(-1)^k \binom{m}{k} = \binom{k-m-1}{k}\ \text{(upper negation)}.
$$

Corollary (even/odd split): $\displaystyle\sum_{k=0}^{n}(-1)^k \binom{n}{k}^2
= \begin{cases}(-1)^{n/2}\binom{n}{n/2}, & n \text{ even},\\ 0, & n \text{ odd}.\end{cases}$

### Plain Language

The parent proves the (unsigned) Vandermonde convolution $\sum_k \binom{m}{k}\binom{n}{r-k}=\binom{m+n}{r}$
and the diagonal corollary $\sum_k \binom{n}{k}^2 = \binom{2n}{n}$. This problem extends
it to signed sums via the upper-negation identity, computing $\sum_k (-1)^k\binom{m}{k}\binom{n}{r-k}$
as the coefficient of $x^r$ in $(1-x)^m(1+x)^n$, and deriving the alternating
sum-of-squares corollary.

### Why This Matters

The signed convolution is the natural companion to the parent's unsigned identity; the
alternating central-binomial corollary $\sum(-1)^k\binom{n}{k}^2$ is a classic result
whose value depends sharply on the parity of $n$, exercising upper negation and
generating-function coefficient extraction.

## Known Results

### What's Already Proven

- Vandermonde convolution $\sum_k \binom{m}{k}\binom{n}{r-k}=\binom{m+n}{r}$ — Mathlib `Nat.add_choose_le` / `Nat.choose_symm_diff`; parent `binomial-theorem-oq-06`.
- $\sum_k \binom{n}{k}^2 = \binom{2n}{n}$ — parent diagonal corollary.
- Binomial theorem `add_pow` / `Commute.add_pow` — Mathlib.

### What's Still Open

- The signed convolution and its parity-dependent alternating sum-of-squares corollary as verified gallery entries.

### Our Goal

Formalize $\sum_{k} (-1)^k \binom{m}{k}\binom{n}{r-k} = [x^r](1-x)^m(1+x)^n$ and the
corollary $\sum_k (-1)^k \binom{n}{k}^2$ with its even/odd split.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| binomial-theorem-oq-06 | Parent: unsigned Vandermonde + $\sum\binom{n}{k}^2=\binom{2n}{n}$ | coefficient comparison |
| binomial-theorem-oq-04-oq-02 | Vandermonde via coefficient comparison | `add_pow`, `Finset.sum` |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Coefficient comparison in $(1-x)^m(1+x)^n$.
   - Why it might work: expand both factors by `add_pow`, multiply, and read off $[x^r]$ via `Finset.sum` manipulation — mirrors the parent's method with a sign.
   - Risk: signs from $(1-x)^m$ and index shifting; casting to `ℤ` to allow negatives.

2. **Approach B**: Upper negation $(-1)^k\binom{m}{k}=\binom{k-m-1}{k}$ then reduce to ordinary Vandermonde.
   - Why it might work: turns the signed sum into an unsigned one already proven.
   - Risk: negative/`Int`-valued binomials; Mathlib support for generalized binomial coefficients.

### Key Difficulties

- Working over `ℤ` (signs) rather than `ℕ`.
- The alternating sum-of-squares corollary needs a parity case split (`Nat.even_or_odd`).

### What Would a Proof Need?

- Key lemma 1: `add_pow` expansions of $(1-x)^m$ and $(1+x)^n$ in `ℤ[X]` (or `Polynomial ℤ`).
- Key lemma 2: coefficient-of-product formula `Polynomial.coeff_mul`.
- Technical requirements: `Finset.sum`, `Polynomial.coeff`, parity split.

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- [Reason for assessment] Signed variant of an already-verified parent; main new ingredient is handling signs over `ℤ`.
- [Similar problems that have been solved] Unsigned Vandermonde and $\sum\binom{n}{k}^2$ are formalized in the parent.
- [Techniques available in Mathlib] `Polynomial.coeff_mul`, `add_pow`, `Nat.choose`, `Finset.sum`.

**Estimated Effort**:
- Exploration: hours
- If tractable: a day
- If hard: unknown (if generalized/`Int` binomials get fiddly)

## References

### Papers
- Graham, Knuth, Patashnik, *Concrete Mathematics*, 1994 — upper negation, Vandermonde.

### Online Resources
- https://en.wikipedia.org/wiki/Vandermonde%27s_identity — signed variants.

### Mathlib
- `Mathlib.Data.Polynomial.Coeff` and `Mathlib.Algebra.BigOperators.NatAntidiagonal` — coefficient convolution.

## Metadata

```yaml
tags:
  - combinatorics
  - binomial-coefficients
  - vandermonde
related_proofs:
  - binomial-theorem-oq-06
  - binomial-theorem-oq-04-oq-02
difficulty: medium
source: gallery-gap
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 7/10
