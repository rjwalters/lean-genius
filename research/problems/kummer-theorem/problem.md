# Problem: Kummer's Theorem on Binomial Divisibility

**Slug**: kummer-theorem
**Created**: 2025-12-31
**Status**: Graduated (Completed)
**Tier**: B

## Problem Statement

### Formal Statement

$$
\nu_p\binom{n}{k} = \text{(number of carries when adding } k + (n-k) \text{ in base } p\text{)}
$$

### Plain Language

The p-adic valuation of a binomial coefficient C(n,k) equals the number of carries when adding k and (n-k) in base p arithmetic.

### Why This Matters

1. **Classical number theory** — Fundamental result connecting binomial coefficients to prime divisibility
2. **Uses Mathlib** — Leverages Nat.Prime.multiplicity_choose
3. **Connected to Lucas theorem** — Both concern binomial coefficients modulo primes

## Known Results

### What's Already Proven

- **Kummer's theorem** — Full proof using Mathlib's multiplicity_choose
- **Lucas theorem connection** — C(n,k) mod p via base-p digit arithmetic
- **Legendre formula** — ν_p(n!) = Σ⌊n/p^i⌋
- **Examples** — C(10,4), C(6,3), C(8,2) with explicit carry counts
- **Prime power divisibility** — When p^k | C(n,m)

### Our Goal

✅ Complete — Proves Kummer's theorem using Mathlib infrastructure.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| None yet | - | - |

## Tractability Assessment

**Significance**: 6/10
**Tractability**: 7/10

## References

### Mathlib
- `Mathlib.NumberTheory.Padics.PadicVal` — p-adic valuation
- `Nat.Prime.multiplicity_choose` — Multiplicity in binomial coefficients

## Metadata

```yaml
tags:
  - number-theory
  - binomial
  - classical
  - p-adic
significance: 6
tractability: 7
tier: B
```
