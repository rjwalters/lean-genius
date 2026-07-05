# Problem: Asymptotic constant for the r-product primitive-set counting function

**Slug**: erdos-793-oq-03
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For the generalized $r$-product primitive-set problem, let $F_r(n)$ denote the maximum
size of a subset of $\{1,\dots,n\}$ containing no element that divides a product of
$r$ others (the $r$-fold generalization of Erdős #793). The question is whether
$$
F_r(n) - \pi(n) \;\sim\; C_r \cdot n^{2/(r+1)} \cdot (\log n)^{-2}
$$
for some constant $C_r > 0$, where $\pi(n)$ is the prime-counting function.

### Plain Language

Erdős Problem #793 concerns primitive sets where no element divides another; the parent
gallery entry formalizes results about primitive sets avoiding product divisibility.
This variant generalizes to the **$r$-product** version — no element divides the product
of $r$ other members — and asks for the precise second-order asymptotic of the extremal
size $F_r(n)$ beyond the leading $\pi(n)$ (the primes in $(n/2, n]$ style contribution):
specifically whether the excess is of order $n^{2/(r+1)}(\log n)^{-2}$ with a constant.

### Why This Matters

Sharp asymptotics for extremal primitive-type sets connect multiplicative number theory,
the distribution of primes, and extremal combinatorics. Pinning the exponent
$2/(r+1)$ and the logarithmic correction — and whether a genuine constant $C_r$ exists —
would sharpen a family of Erdős-style extremal problems and clarify how the answer scales
with the product length $r$.

## Known Results

### What's Already Proven

- Base results on primitive sets avoiding product divisibility — gallery proof
  `erdos-793` (Erdős Problem #793).
- Classical primitive-set density bounds (Erdős 1935; Behrend; Erdős–Sárközy–Szemerédi).

### What's Still Open

- The exact exponent for $F_r(n)-\pi(n)$ in the $r$-product setting.
- Existence and value of the constant $C_r$ in the conjectured asymptotic.
- Matching upper and lower bounds establishing the $(\log n)^{-2}$ correction.

### Our Goal

This is a hard analytic-number-theory asymptotic. A tractable formalization target is
a **rigorous one-sided bound**: e.g. an upper bound $F_r(n) - \pi(n) = O(n^{2/(r+1)})$,
or the leading-order lower bound via an explicit construction, rather than the full
sharp constant.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-793 | Parent problem — primitive sets, product divisibility | multiplicative structure, extremal counting |
| infinitude-primes / prime-counting entries | $\pi(n)$ asymptotics used in the excess term | PNT-style estimates |

## Initial Thoughts

### Potential Approaches

1. **Approach A — one-sided upper bound via a counting/sieve argument**:
   Bound the number of admissible non-prime elements by an $r$-product-free counting
   argument, targeting $O(n^{2/(r+1)})$ without the exact constant.
   - Why it might work: exponents are often reachable even when constants are not.
   - Risk: the $(\log n)^{-2}$ factor requires delicate sieve control.

2. **Approach B — explicit construction for the lower bound**:
   Construct an $r$-product-free set of near-primes of size $\gg n^{2/(r+1)}(\log n)^{-2}$.
   - Why it might work: constructive lower bounds are more amenable to formalization.
   - Risk: verifying the product-free property over the whole construction.

### Key Difficulties

- The sharp constant $C_r$ is likely out of reach for full formalization.
- Analytic estimates (PNT-level, sieve bounds) are heavy to formalize in Lean.

### What Would a Proof Need?

- Key lemma 1: an $r$-product-free upper-bound counting lemma with exponent $2/(r+1)$.
- Key lemma 2: prime-counting asymptotics for the $\pi(n)$ subtraction.
- Technical requirements: Mathlib analytic-NT support (PNT is partially available).

## Tractability Assessment

**Difficulty**: Moonshot (full statement); Medium–High for a one-sided exponent bound

**Justification**:
- The sharp asymptotic with constant $C_r$ is genuine open research.
- A rigorous one-sided $O(n^{2/(r+1)})$ or matching construction is a realistic scope.
- Heavy analytic estimates limit how much can be fully machine-checked.

**Estimated Effort**:
- Exploration: 2–4 days scoping a provable sub-claim
- If tractable (one-sided bound): weeks
- If hard (sharp constant): unknown / research-grade

## References

### Papers
- Erdős, *Note on sequences of integers no one of which is divisible by any other* (1935).
- Erdős, Sárközy, Szemerédi — primitive sequences and density.
- The Erdős Problems project entry for #793.

### Online Resources
- https://www.erdosproblems.com/793 — problem statement and status.

### Mathlib
- `Mathlib.NumberTheory.PrimeCounting` — $\pi(n)$ and PNT-adjacent estimates.
- `Nat.factorization`, divisibility API — for product-divisibility conditions.

## Metadata

```yaml
tags:
  - number-theory
  - erdos
  - primitive-sets
  - analytic-number-theory
  - divisibility
related_proofs:
  - erdos-793
difficulty: moonshot
source: gallery-gap
created: 2026-07-04
```

**Significance**: 6/10
**Tractability**: 4/10
