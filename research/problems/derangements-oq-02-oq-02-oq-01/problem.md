# Problem: Higher Moments of Fixed Points of a Random Permutation

**Slug**: derangements-oq-02-oq-02-oq-01
**Created**: 2026-06-18
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $F_n : S_n \to \mathbb{N}$ count the fixed points of a permutation, with $S_n$ uniform. The $k$-th factorial moment is exactly $1$ for $n \ge k$:

$$
\mathbb{E}\big[\,(F_n)_k\,\big] \;=\; \mathbb{E}\big[\,F_n (F_n-1)\cdots(F_n-k+1)\,\big] \;=\; 1, \qquad n \ge k,
$$

and consequently the ordinary moments are the Bell-number / Dobinski partial sums, e.g. $\mathbb{E}[F_n] = 1$, $\mathbb{E}[F_n^2] = 2$, $\mathbb{E}[F_n^3] = 5$, matching the Poisson(1) limit moments for $n \ge k$.

### Plain Language

Pick a permutation of $\{1,\dots,n\}$ at random. The number of elements it leaves fixed is a random variable. Its average is $1$. We want machine-checked formulas for the higher moments $\mathbb{E}[F_n^k]$ (and the cleaner factorial moments, which equal $1$), establishing the standard convergence to a Poisson(1) distribution.

### Why This Matters

Extends the gallery's expected-fixed-points result (`derangements-oq-02-oq-02`) from the mean to all moments. The factorial-moment-equals-one identity is the clean combinatorial heart of the derangement/Poisson connection and a satisfying formalization of a textbook probability fact.

## Known Results

### What's Already Proven

- `derangements-oq-02-oq-02` ("Expected Fixed Points of a Random Permutation") — establishes $\mathbb{E}[F_n] = 1$ and the counting framework.
- Mathlib `Equiv.Perm`, `Fintype.card`, and derangement counts (`Nat.derangements` / `numDerangements`).

### What's Still Open

- The factorial-moment identity $\mathbb{E}[(F_n)_k] = 1$ for $k \ge 2$.
- Ordinary moments $\mathbb{E}[F_n^k]$ as Bell-number partial sums and the Poisson(1) moment match.

### Our Goal

Prove $\mathbb{E}[(F_n)_k] = 1$ for $n \ge k$ by the indicator/linearity-of-expectation argument: a falling-factorial of fixed-point counts equals the number of ordered $k$-tuples of distinct fixed points, whose expectation telescopes to $1$. Then derive $\mathbb{E}[F_n^2] = 2$ as the first new explicit corollary.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| derangements-oq-02-oq-02 | Mean fixed-point count; same probability framing | linearity of expectation, Burnside |
| derangements (parent family) | Derangement counts and inclusion–exclusion | inclusion–exclusion, generating functions |

## Initial Thoughts

### Potential Approaches

1. **Approach A — falling factorial via ordered tuples**: show $\sum_{\sigma} (F_n(\sigma))_k = k! \cdot \binom{n}{k} \cdot$ (count of permutations fixing a chosen $k$-set) $= n!$ , so the average of $(F_n)_k$ is $1$. Why it might work: each factor counts injections into the fixed-point set; the identity is purely combinatorial. Risk: bookkeeping over ordered tuples in Lean.
2. **Approach B — generating function / EGF**: use $\sum_n \mathbb{E}[z^{F_n}] \frac{t^n}{n!}$ relation. Why it might work: clean algebra. Risk: Mathlib EGF support is thinner than direct counting.

### Key Difficulties

- Encoding the falling factorial of a counting function and relating it to injections.
- Working with rational expectations over `Fintype S_n`.

### What Would a Proof Need?

- Lemma: $\sum_{\sigma \in S_n} (F_n(\sigma))_k = n!$ for $n \ge k$ (the core identity).
- Conversion to expectation by dividing by $|S_n| = n!$.
- Corollary: $\mathbb{E}[F_n^2] = 2$ via $F_n^2 = (F_n)_2 + F_n$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mean case is already done; the higher-moment argument is a natural, well-known generalization.
- Mathlib has the permutation/fixed-point and counting infrastructure.
- Main risk is combinatorial bookkeeping, not missing theory.

**Estimated Effort**:
- Exploration: hours
- If tractable: 2–4 days
- If hard: 1–2 weeks (if EGF machinery is needed)

## References

### Papers
- M. Bóna, *Combinatorics of Permutations* — fixed points and the Poisson limit.

### Online Resources
- Standard treatment: factorial moments of fixed-point counts equal $1$ (Poisson(1) limit).

### Mathlib
- `Mathlib.Combinatorics.Derangements.Basic` / `.Finite` — derangement counts.
- `Mathlib.GroupTheory.Perm.*`, `Equiv.Perm.fixedPoints` — fixed-point sets.

## Metadata

```yaml
tags:
  - combinatorics
  - permutations
  - derangements
  - probability
  - factorial-moments
related_proofs:
  - derangements-oq-02-oq-02
difficulty: medium
source: proof-suggestion
created: 2026-06-18
```
