# Problem: q-Vandermonde Identity for Gaussian Binomial Coefficients

**Slug**: binomial-theorem-oq-04-oq-02-oq-01
**Created**: 2026-04-21T06:01:53-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The q-Vandermonde (Gauss-Vandermonde) identity states:

$$
\binom{m+n}{r}_q = \sum_{k=0}^{r} q^{k(m-r+k)} \binom{m}{r-k}_q \binom{n}{k}_q
$$

where $\binom{n}{k}_q = \frac{(q;q)_n}{(q;q)_k (q;q)_{n-k}}$ are the Gaussian binomial coefficients (q-binomial coefficients).

Equivalently, in the form without the $q^{k(m-r+k)}$ twist:

$$
\binom{m+n}{r}_q = \sum_{k=0}^{r} q^{(r-k)(n-k)} \binom{m}{k}_q \binom{n}{r-k}_q
$$

As a Lean theorem:

```lean
theorem q_vandermonde (q : ℝ) (hq : q ≠ 1) (m n r : ℕ) :
    gaussBinom q (m + n) r = ∑ k ∈ Finset.range (r + 1),
      q ^ (k * (m - r + k)) * gaussBinom q m (r - k) * gaussBinom q n k := by
  sorry
```

### Plain Language

The classical Vandermonde identity $\binom{m+n}{r} = \sum_k \binom{m}{k}\binom{n}{r-k}$
counts ways to choose $r$ items from $m+n$ by splitting across two groups. The
q-Vandermonde identity is its q-analog: it replaces binomial coefficients with
Gaussian binomial coefficients (which count subspaces of vector spaces over $\mathbb{F}_q$)
and introduces a $q$-weight factor that tracks the relative position of chosen subspaces.

At $q=1$, the Gaussian binomials reduce to ordinary binomials and the identity
recovers the classical Vandermonde identity.

### Why This Matters

- Gaussian binomial coefficients count $k$-dimensional subspaces of $\mathbb{F}_q^n$
- The q-Vandermonde identity is foundational for q-series theory and quantum groups
- It appears in representation theory, combinatorics of partitions, and physics (integrable systems)
- Fills a gap in Mathlib's q-analog theory adjacent to the existing binomial theorem formalization

## Known Results

### What's Already Proven

- Classical Vandermonde identity `Nat.add_choose_eq` — in Mathlib
- Gaussian binomial coefficients `Nat.gaussBinom` — in Mathlib (GaussianBinomial.lean)
- Basic recurrence for Gaussian binomials — in Mathlib
- `GaussianBinomial.lean` contains `gaussBinom_add_succ_right` and related lemmas

### What's Still Open

- The q-Vandermonde convolution identity itself is not yet in Mathlib
- The generating function interpretation over $\mathbb{F}_q^n$ vector spaces

### Our Goal

Prove the q-Vandermonde identity for Gaussian binomial coefficients in Lean/Mathlib,
connecting it to the existing `Nat.gaussBinom` infrastructure.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `binomial-theorem` | Parent proof; classical Vandermonde already handled | Binomial coefficients, Finset.sum |
| `arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02` | Multiset Vandermonde — parallel combinatorial identity | Finset convolutions |

## Initial Thoughts

### Potential Approaches

1. **Induction on r (Pascal recurrence)**
   - The Gaussian binomial satisfies $\binom{n}{k}_q = \binom{n-1}{k-1}_q + q^k \binom{n-1}{k}_q$
   - Use this recurrence to prove the q-Vandermonde by induction on $r$, matching the
     classical Vandermonde proof structure
   - Why it might work: direct parallel to classical proof; recurrence is in Mathlib
   - Risk: bookkeeping of q-powers is intricate

2. **Generating function / polynomial identity**
   - The identity follows from $(1+qx)(1+q^2x)\cdots(1+q^m x)(1+qx)\cdots(1+q^n x)$
     expansion as polynomials in $q$
   - Risk: requires formalizing polynomial manipulations over q

3. **Direct combinatorial bijection**
   - Interpret both sides as counting subspaces of $\mathbb{F}_q^{m+n}$
   - Risk: requires finite field infrastructure in Mathlib

### Key Difficulties

- Correct handling of $q$-power exponents in the twisted sum
- The `gaussBinom` API in Mathlib may not have all needed lemmas
- Edge cases when $q = 0$ or $q = 1$ (limit to classical case)

### What Would a Proof Need?

- Pascal recurrence: `gaussBinom_succ_succ` or equivalent
- Finset sum manipulation: shifting index, splitting sums
- Algebraic identity: factoring out q-powers

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The classical Vandermonde proof is well-understood and parallelizes to q-setting
- Mathlib already has `Nat.gaussBinom` with recurrences
- The main challenge is tracking q-exponent arithmetic, which is mechanical
- Similar algebraic identities have been successfully formalized in Lean

**Estimated Effort**:
- Exploration (OBSERVE/ORIENT): 1-2 days
- Proof attempt (DECIDE/ACT): 2-5 days

## References

### Papers
- Gasper & Rahman, "Basic Hypergeometric Series" (2nd ed., 2004) — definitive reference
- Andrews, "The Theory of Partitions" — Chapter 3 covers q-Vandermonde

### Mathlib
- `Mathlib.RingTheory.GaussianBinomial` — `gaussBinom` definition and recurrences
- `Mathlib.Data.Nat.Choose.Vandermonde` — classical Vandermonde identity

## Metadata

```yaml
tags:
  - combinatorics
  - q-analogs
  - gaussian-binomials
  - vandermonde
  - q-series
related_proofs:
  - binomial-theorem
difficulty: medium
source: gallery-gap
created: 2026-04-21T06:01:53-07:00
```

**Significance**: 7/10
**Tractability**: 6/10
