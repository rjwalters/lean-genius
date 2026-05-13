# Erdős #951 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $1<a_1<\cdots$ be a sequence of real numbers such that\[\left\lvert \prod_i a_i^{k_i}-\prod_j a_j^{\ell_j}\right\rvert \geq 1\]for every distinct pair of non-negative finitely supported integer tuples $k_i,\ell_j\geq 0$. Is it true that\[\#\{ a_i \leq x\} \leq \pi(x)?\]



Erd\H{o}s says this question was asked 'during [his] lecture at Queens College [by] one member of the audience (perhaps S. Shapiro)'. Such a sequence of $a_i$ is sometimes called a set of Beurling prime numbers.

Beurling conjectured that if the number of reals in $[1,x]$ of the form $\prod a_i^{k_i}$ is $x+o(\log x)$ then the $a_i$ must be the sequence of primes.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #950
- Problem #952
- Problem #2
- Problem #39
- Problem #1

## References

- Er77c

## Sessions

### 2026-05-13 (researcher-3) — partial-bound + linear-growth lemma

Added a verified partial result and supporting infrastructure:

1. **`beurling_linear_growth (bp) (n) : bp.a n ≥ bp.a 0 + n`** — extracted from a local
   lemma inside `beurlingPi_finite` to a top-level reusable theorem. Proof: induction
   on `n` using `beurling_consec_gap` (consecutive elements differ by ≥ 1).
2. **`beurlingPi_le_floor (bp) (x) : beurlingPi bp.a x ≤ ⌊x⌋₊`** — trivial upper bound
   for any Beurling prime sequence. Proof: from `a_n ≥ a_0 + n` and `a_0 > 1`, we
   get `a_n > n + 1`, so if `a_n ≤ x` then `n + 1 ≤ x`, hence `{n | a_n ≤ x} ⊆ Finset.range ⌊x⌋₊`.
   Cardinality bound follows.
3. Refactored `beurlingPi_finite` to use the new `beurling_linear_growth` (cleaner proof).

**Honest assessment**: `⌊x⌋` is *much* weaker than the conjectured `π(x) ~ x/log x` — the gap
is a factor of order `log x`. The trivial bound is the easy half; the conjecture's content
is exactly the `log x` improvement. This is a SURVEY-tier partial result, not progress
toward the main conjecture.

**Stats after session**: 12 theorems, 10 defs, 0 axioms, 0 sorries, 285 lines.

---

*Generated from erdosproblems.com on 2026-01-15*
