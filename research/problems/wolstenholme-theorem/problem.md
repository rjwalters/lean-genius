# Problem: Wolstenholme's Theorem

**Slug**: wolstenholme-theorem
**Created**: 2025-12-31
**Status**: Graduated (Completed)
**Tier**: B

## Problem Statement

### Formal Statement

$$
p \geq 5 \text{ prime} \Rightarrow \binom{2p-1}{p-1} \equiv 1 \pmod{p^3}
$$

### Plain Language

For primes p ≥ 5, the central binomial coefficient C(2p-1, p-1) is congruent to 1 modulo p³. This is a deep divisibility result for binomial coefficients.

### Why This Matters

1. **Classical number theory** — One of the deepest binomial divisibility results
2. **Wolstenholme primes** — Only 2 known: 16843, 2124679 (where p^4 divides)
3. **Babbage's theorem** — Related mod p² result for p ≥ 3

## Known Results

### What's Already Proven

- **Computational verification** — p = 5, 7, 11, 13 verified
- **Babbage's theorem** — C(2p-1, p-1) ≡ 1 (mod p²) for p ≥ 3
- **Failure cases** — p = 2, 3 don't satisfy the theorem
- **Wolstenholme primes** — Definition formalized
- **Harmonic number connection** — Link to harmonic sums

### Our Goal

✅ Complete — Verified instances and related theorems.

## Tractability Assessment

**Significance**: 6/10
**Tractability**: 7/10

## Metadata

```yaml
tags:
  - number-theory
  - binomial
  - classical
  - wolstenholme
significance: 6
tractability: 7
tier: B
```
