# Problem: Connect the rising (parallel) Vandermonde to the standard Vandermonde convolution

## Statement

### Plain Language

The parent entry (`arithmetic-series-oq-02-oq-02`, "2D Hockey Stick
Identity") proves a *rising* / *parallel* form of the Vandermonde
convolution,

> `parallel_vandermonde`: ∑_{i+j=n} C(i+a, a)·C(j+b, b) = C(n+a+b+1, a+b+1),

by induction on `n`
(`proofs/Proofs/ArithmeticSeriesOQ02OQ02.lean:61`).

This open question asks: connect that rising identity to the **standard
Vandermonde convolution**

> ∑_{i+j=k} C(m, i)·C(s, j) = C(m+s, k)

via generating functions or a direct combinatorial argument.

### Formal Statement

$$
\sum_{i+j=n} \binom{i+a}{a}\binom{j+b}{b}
\;=\;\binom{n+a+b+1}{a+b+1}
\quad\Longleftrightarrow\quad
\binom{m+s}{k}=\sum_{i+j=k}\binom{m}{i}\binom{s}{j}.
$$

## Classification

```yaml
tier: B
significance: 6
tractability: 5
tags:
  - seeker-selected
  - combinatorics
  - binomial-coefficients
  - vandermonde
  - generating-functions
```

**Significance**: 6/10
**Tractability**: 5/10

## Why This Matters

1. The standard Vandermonde convolution is already in Mathlib as
   `Nat.add_choose_eq` (see ORIENT finding). Establishing the precise
   bridge clarifies that the project's `parallel_vandermonde` is not an
   independent fact but the **upper-negation dual** of the Mathlib lemma.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| arithmetic-series-oq-02-oq-02 (2D Hockey Stick) | parent; proves `parallel_vandermonde` by induction |
