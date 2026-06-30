# Problem: Combinatorial (Visual) Proof of Nicomachus's Theorem

**Slug**: sum-of-kth-powers-oq-03
**Created**: 2026-06-14
**Status**: Active (OBSERVE)
**Source**: gallery-gap (parent: `sum-of-kth-powers`)

## Problem Statement

### Formal Statement

Nicomachus's theorem:

$$
\sum_{i=1}^{n} i^3 = \left(\sum_{i=1}^{n} i\right)^2 = \binom{n+1}{2}^2.
$$

The parent gallery proof (`sum-of-kth-powers`, Faulhaber) establishes this algebraically. This
problem asks for an **independent combinatorial proof** based on the classical odd-number
partition: $i^3$ equals the sum of $i$ consecutive odd numbers, and laying these out yields
exactly the first $\binom{n+1}{2}$ odd numbers, whose sum is $\binom{n+1}{2}^2$. Concretely,

$$
i^3 = \sum_{j=0}^{i-1}\big(i^2 - i + 1 + 2j\big), \qquad
\sum_{i=1}^n i^3 = \sum_{m=1}^{T_n} (2m-1) = T_n^2,\quad T_n=\tfrac{n(n+1)}2 .
$$

### Plain Language

There is a well-known "visual" proof that $1^3+2^3+\dots+n^3$ is a perfect square: each cube
$i^3$ is a block of $i$ odd numbers, and stacking them up reproduces the first $T_n$ odd numbers
$1,3,5,\dots$, which always sum to a square. The goal is to formalize *this* argument in Lean as a
second, structurally different proof of the same identity the gallery already proves algebraically.

### Why This Matters

Two genuinely independent proofs of one theorem are pedagogically and mathematically valuable, and
the gallery explicitly prizes multiple-proof entries. The combinatorial proof exercises a reusable
lemma — "the odd numbers partition the cubes" — and the bijection between $\{(i,j)\}$ and an initial
segment of odd numbers, which is a clean finite-combinatorics formalization target.

## Known Results

### What's Already Proven

- `sum-of-kth-powers` — Faulhaber/algebraic proof of $\sum i^3 = T_n^2$ and general power sums (parent).
- Mathlib: `Finset.sum_range_id`, `Finset.sum_range_succ`, `Finset.sum_range_id_mul_two`, and `Gauss sum` lemmas; sum of first $n$ odd numbers $= n^2$ is provable via `Finset.sum`.

### What's Still Open (in this gallery)

- A formalized "$i^3 =$ sum of $i$ specific consecutive odds" decomposition.
- The bijection identifying $\bigcup_i (\text{odds for } i^3)$ with the first $T_n$ odd numbers.

### Our Goal

Prove `∑ i in range (n+1), i^3 = (∑ i in range (n+1), i)^2` in Lean **via the odd-number
partition**, producing a `Finset` bijection or reindexing argument, and place it alongside the
existing algebraic proof as an independent derivation.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sum-of-kth-powers | Direct parent; algebraic proof of the same identity | Faulhaber, induction |
| arithmetic-series | Sum of an AP; sum of first $n$ odds $= n^2$ | telescoping, Gauss pairing |
| sum-of-squares (gallery) | Companion power-sum identity | induction, closed form |

## Initial Thoughts

### Potential Approaches

1. **Odd-number reindexing (recommended)**: prove $i^3 = \sum_{j} (\text{odd block})$, then sum over $i$
   and recognize the result as $\sum_{m=1}^{T_n}(2m-1)=T_n^2$.
   - Why it might work: every step is a finite `Finset.sum` identity provable by `induction`/`ring`/`omega`.
   - Risk: getting the block's starting odd number $(i^2-i+1)$ and the reindexing offsets exactly right.

2. **Explicit bijection**: build `Finset` bijection between $\{(i,j): 1\le i\le n, 0\le j<i\}$ and $\{1,\dots,T_n\}$ and transport the sum.
   - Why it might work: makes the "visual" content literal.
   - Risk: bijection bookkeeping is heavier than the reindexing route.

### Key Difficulties

- Pinning down the first odd number in the block for $i^3$ and proving the blocks tile the odds without gaps or overlaps.
- Keeping the proof genuinely distinct from the algebraic one (not silently collapsing to induction on the closed form).

### What Would a Proof Need?

- Key lemma 1: $i^3 = \sum_{j=0}^{i-1}\big(i^2-i+1+2j\big)$.
- Key lemma 2: $\sum_{m=1}^{N}(2m-1) = N^2$ with $N=T_n$.
- Technical requirements: `Finset.sum_range`, `Finset.sum_bij`, `ring`, `omega`.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Pure finite combinatorics with closed forms; no external theory required.
- Mathlib's `Finset.sum` API covers every needed manipulation.
- A clean, self-contained target ideal for a fast-path formalization.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days
- If hard: under a week

## References

### Papers
- Nicomachus of Gerasa, *Introduction to Arithmetic* (c. 100 AD).
- Conway & Guy, *The Book of Numbers* — visual proof of the sum-of-cubes identity.

### Online Resources
- Parent gallery entry `sum-of-kth-powers`.

### Mathlib
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum` reindexing and bijections.
- `Mathlib.Algebra.BigOperators.Intervals` — sums over ranges.

## Metadata

```yaml
tags:
  - combinatorics
  - power-sums
  - bijective-proof
  - nicomachus
related_proofs:
  - sum-of-kth-powers
  - arithmetic-series
difficulty: low
source: proof-suggestion
created: 2026-06-14
```
