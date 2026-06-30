# Problem: Central binomial as a sum of squared binomials

**Slug**: binomial-theorem-oq-04-oq-02-oq-03
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\binom{2n}{n} = \sum_{k=0}^{n} \binom{n}{k}^2 \qquad (n \in \mathbb{N})
$$

### Plain Language

The central binomial coefficient counts the number of ways to choose $n$ items
from $2n$. Splitting the $2n$ items into two halves of size $n$ and summing over
how many come from the first half gives the right-hand sum, where
$\binom{n}{k}^2 = \binom{n}{k}\binom{n}{n-k}$. The goal is a machine-checked,
axiom-free proof of this identity (the diagonal case of the Chu–Vandermonde
identity).

### Why This Matters

This is one of the most-cited combinatorial identities: it underlies the
asymptotics of $\binom{2n}{n}\sim 4^n/\sqrt{\pi n}$, the theory of Catalan
numbers, and random-walk return probabilities. It is a clean, self-contained
sibling of the parent gallery proof (binomial-theorem-oq-04-oq-02) and a good
showcase of Mathlib's `Nat.choose` API.

## Known Results

### What's Already Proven

- Chu–Vandermonde / Vandermonde's identity in Mathlib: `Nat.add_choose_eq`
  (and `Nat.choose_symm`, `Nat.choose_symm_diff`).
- The parent gallery proof `binomial-theorem-oq-04-oq-02` establishes the
  surrounding binomial-coefficient machinery (verified, 0-axiom).

### What's Still Open

- A direct, registered Lean statement
  `∑ k in range (n+1), (n.choose k)^2 = (2*n).choose n`.
- Optionally, the bijective / double-counting narrative alongside the algebraic
  Vandermonde route.

### Our Goal

Produce a verified, 0-axiom Lean proof of
`∑ k ∈ Finset.range (n+1), (Nat.choose n k)^2 = Nat.choose (2*n) n`,
reducing it to `Nat.add_choose_eq` with `a = b = n`, `k = n` and rewriting
`n.choose (n-k) = n.choose k` via `Nat.choose_symm`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| binomial-theorem-oq-04-oq-02 | Direct parent; Vandermonde scaffolding | binomial coefficients |
| combinations-formula-oq-02-oq-01 | Catalan generating function uses central binomials | generating functions |

## Initial Thoughts

### Potential Approaches

1. **Vandermonde specialization**: instantiate `Nat.add_choose_eq` at $a=b=n$,
   $k=n$; convert $\binom{n}{n-k}$ into $\binom{n}{k}$ with `Nat.choose_symm`.
   - Why it might work: Mathlib already proves the general convolution.
   - Risk: index bookkeeping over `Finset.antidiagonal` vs `Finset.range`.

2. **Generating functions**: extract $[x^n]$ from $(1+x)^n(1+x)^n=(1+x)^{2n}$.
   - Why it might work: matches the parent proof's polynomial framing.
   - Risk: heavier `PowerSeries`/`Polynomial.coeff` plumbing than needed.

### Key Difficulties

- Reconciling the antidiagonal form of Mathlib's Vandermonde with the
  `range (n+1)` summation index.
- Keeping everything in $\mathbb{N}$ (no subtraction traps) or casting cleanly
  to $\mathbb{Z}$.

### What Would a Proof Need?

- Key lemma 1: `Nat.add_choose_eq` (Vandermonde convolution).
- Key lemma 2: `Nat.choose_symm` to turn $\binom{n}{n-k}$ into $\binom{n}{k}$.
- Technical requirements: a reindexing lemma between `antidiagonal n` and
  `range (n+1)`.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The general Vandermonde identity is already in Mathlib; this is its diagonal.
- Similar diagonal/symmetry identities have been formalized in the gallery.
- All required lemmas (`Nat.add_choose_eq`, `Nat.choose_symm`) exist.

**Estimated Effort**:
- Exploration: a few hours
- If tractable: 1–2 days

## References

### Mathlib
- `Mathlib.Combinatorics.Choose.Vandermonde` — `Nat.add_choose_eq`.
- `Mathlib.Data.Nat.Choose.Basic` — `Nat.choose_symm`, `Nat.choose_symm_diff`.

## Metadata

```yaml
tags:
  - combinatorics
  - binomial-coefficients
  - vandermonde
  - classic
related_proofs:
  - binomial-theorem-oq-04-oq-02
  - combinations-formula-oq-02-oq-01
difficulty: low
source: gallery-gap
created: 2026-06-24
```
