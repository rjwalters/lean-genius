# Problem: Multiplicativity of σ*(n) and the r₄ Divisor-Sum Closed Form

**Slug**: four-square-distribution-oq-06-oq-02
**Created**: 2026-07-02
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\sigma^*(n) := \sum_{\substack{d \mid n \\ 4 \nmid d}} d
\quad\text{is multiplicative, and writing } n = 2^k m \ (m \text{ odd}):
\quad
\sigma^*(n) =
\begin{cases}
\sigma(m), & k = 0,\\[2pt]
3\,\sigma(m), & k \ge 1,
\end{cases}
$$

where $\sigma(m)=\sum_{d\mid m} d$ is the ordinary sum-of-divisors.

### Plain Language

The parent entry computes $\sigma^*(n) = \sum_{4 \nmid d \mid n} d$ (equivalently
$\text{jacobiR4}(n)/8$) on prime powers. This problem assembles those local values into
a single global formula by proving $\sigma^*$ is multiplicative and evaluating the
power-of-2 part: the odd part contributes $\sigma(m)$, and any positive power of $2$
contributes a uniform factor of $3$.

### Why This Matters

This closes the gap between the parent's prime-power values and arbitrary $n$ on the
arithmetic side of Jacobi's four-square theorem $r_4(n) = 8\,\sigma^*(n)$ — reducing the
whole arithmetic side to the classical multiplicative $\sigma$, and isolating exactly
what remains (the geometric count $r_4(n)$ itself) for the full Jacobi formalization.

## Known Results

### What's Already Proven

- Prime-power values of $\sigma^*$ — parent `four-square-distribution-oq-06`.
- $\sigma$ (sum of divisors) is multiplicative — Mathlib `Nat.ArithmeticFunction.sigma` / `isMultiplicative_sigma`.
- $\sigma^*(2^k) = 3$ for $k \ge 1$ and $\sigma^*(2^0)=1$ (from $\{1\}$; $4\nmid d$ kills $4,8,\dots$).

### What's Still Open

- Multiplicativity of $\sigma^*$ and the assembled $\sigma^*(n) = 3^{[k\ge1]}\,\sigma(m)$ closed form.
- (Separately, the genuinely hard target $r_4(n)=8\sigma^*(n)$ itself — out of scope here.)

### Our Goal

Prove $\sigma^*$ is multiplicative (as an `ArithmeticFunction`) and derive
$\sigma^*(2^k m) = \sigma(m)$ for $k=0$, $3\sigma(m)$ for $k\ge 1$, with $m$ odd. Stay on
the arithmetic side (no theta functions).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| four-square-distribution-oq-06 | Parent: prime-power values of σ* | divisor sums, `divisors_prime_pow` |
| four-square-distribution-oq-06-oq-01 | Sibling: assembling σ* pieces | multiplicative arithmetic functions |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Express $\sigma^*$ as a Dirichlet-style/product-friendly arithmetic function and invoke Mathlib's multiplicative machinery.
   - Why it might work: $\sigma^*(n) = \sigma(n) - 4\sigma(n/4)$-type relations reduce to $\sigma$, which is already multiplicative in Mathlib.
   - Risk: getting the "$4 \nmid d$" filter into a form Mathlib's `IsMultiplicative` lemmas accept.

2. **Approach B**: Direct proof via the CRT decomposition of `Nat.divisors (a*b)` for coprime `a,b`.
   - Why it might work: `Nat.Coprime.sum_divisors_mul` / `divisors_mul` give the factorization of divisor sums; the $4\nmid d$ condition factors through the 2-part.
   - Risk: bookkeeping on the $4\nmid d$ predicate under the coprime split.

### Key Difficulties

- Encoding the filtered divisor sum $\sum_{4\nmid d\mid n} d$ as a Mathlib arithmetic function.
- Handling the 2-adic valuation split $n = 2^k m$ cleanly.

### What Would a Proof Need?

- Key lemma 1: $\sigma$ multiplicative (`Nat.ArithmeticFunction.isMultiplicative_sigma`).
- Key lemma 2: $\sigma^*(2^k) = 3$ for $k\ge1$, $=1$ for $k=0$ (finite computation).
- Technical requirements: `Nat.Coprime` divisor factorization, `Nat.factorization`/2-adic valuation.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- [Reason for assessment] Leans on Mathlib's multiplicative-function API; the only novelty is the $4\nmid d$ filter and the 2-part evaluation.
- [Similar problems that have been solved] The parent prime-power computation and Mathlib's `sigma` multiplicativity.
- [Techniques available in Mathlib] `ArithmeticFunction.IsMultiplicative`, `Nat.divisors`, `Nat.Coprime.divisors_mul`, `Nat.factorization`.

**Estimated Effort**:
- Exploration: hours to a day
- If tractable: a few days
- If hard: unknown (if the filtered function resists Mathlib's multiplicative lemmas)

## References

### Papers
- Hardy & Wright, *An Introduction to the Theory of Numbers* — Jacobi four-square theorem and $\sigma$.

### Online Resources
- https://en.wikipedia.org/wiki/Jacobi%27s_four-square_theorem — $r_4(n)=8\sigma^*(n)$.

### Mathlib
- `Mathlib.NumberTheory.ArithmeticFunction` — `sigma`, `IsMultiplicative`, divisor sums.

## Metadata

```yaml
tags:
  - number-theory
  - sum-of-squares
  - multiplicative-functions
related_proofs:
  - four-square-distribution-oq-06
  - four-square-distribution-oq-06-oq-01
difficulty: medium
source: gallery-gap
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 6/10
