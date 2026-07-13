# Problem: p-step shallow diagonals of Pascal's triangle give the p-bonacci sequences

**Slug**: combinations-formula-oq-01-oq-01-oq-02
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a step parameter $p \ge 1$, the **$p$-step shallow-diagonal sums** of Pascal's triangle
$$
G^{(p)}_{n} \;=\; \sum_{j \ge 0} \binom{n - (p-1)j}{\,j\,}
$$
satisfy the $p$-bonacci recurrence $G^{(p)}_{n} = G^{(p)}_{n-1} + G^{(p)}_{n-p}$ (with appropriate seeds), recovering the Fibonacci numbers when $p = 2$ and the generalized ($p$-bonacci) Fibonacci sequences for larger $p$.

### Plain Language

The parent proves the classic fact that summing $\binom{n-j}{j}$ along the **shallow diagonals** of Pascal's triangle yields the Fibonacci numbers $F(n+1)$. This leaf generalizes the slope of the diagonal: taking $p$-step diagonals produces the **$p$-bonacci** sequences (tribonacci for $p=3$, etc.), each satisfying a depth-$p$ linear recurrence. The goal is to state and prove the closed shallow-diagonal sum and its $p$-bonacci recurrence.

### Why This Matters

Extends a well-known Fibonacci identity into a clean parametric family, connecting binomial-coefficient sums to higher-order linear recurrences — a recurring theme in combinatorics and a good Mathlib `Nat.choose` / `Finset.sum` exercise.

## Known Results

### What's Already Proven

- Parent `combinations-formula-oq-01-oq-01` — Fibonacci shallow-diagonal sum $\sum_j \binom{n-j}{j} = F(n+1)$.
- Sibling `combinations-formula-oq-01-oq-01-oq-01` — related diagonal-sum work (verify scope to avoid overlap).
- Mathlib: `Nat.choose`, `Nat.fib`, `Finset.sum` manipulation, antidiagonal/Pascal recurrence (`Nat.choose_succ_succ`).

### What's Still Open

- The $p$-step diagonal sum and its depth-$p$ recurrence as named theorems.
- A Mathlib-friendly definition of the $p$-bonacci sequence (or proof the sum satisfies the recurrence directly).

### Our Goal

Define the $p$-step shallow-diagonal sum, prove the $p$-bonacci recurrence it satisfies (generalizing the parent $p=2$ Fibonacci case), axiom-free.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| combinations-formula-oq-01-oq-01 | Parent: Fibonacci shallow-diagonal sum | `Nat.choose`, Pascal recurrence, induction |
| combinations-formula-oq-01 | Combinations identities umbrella | binomial sums |

## Initial Thoughts

### Potential Approaches

1. **Approach A — recurrence by Pascal's rule**: Split $\binom{n-(p-1)j}{j}$ via `Nat.choose_succ_succ` and reindex to show $G^{(p)}_n = G^{(p)}_{n-1} + G^{(p)}_{n-p}$ directly.
   - Why it might work: mirrors the parent's $p=2$ proof; purely combinatorial.
   - Risk: index/bounds bookkeeping is heavier for general $p$ (off-by-$p$ shifts).

2. **Approach B — generating functions**: Identify $\sum_n G^{(p)}_n x^n$ with $1/(1 - x - x^p)$.
   - Why it might work: clean once set up; the GF directly encodes the recurrence.
   - Risk: power-series formalization overhead in Mathlib.

### Key Difficulties

- Choosing the cleanest definition of the $p$-bonacci sequence in Lean.
- Reindexing the binomial sum under the $p$-dependent shift.

### What Would a Proof Need?

- Key lemma 1: Pascal's rule applied to the shifted binomial term.
- Key lemma 2: reindexing `Finset.sum` to expose the depth-$p$ recurrence.
- Technical requirements: a definition of $G^{(p)}$ and the target recurrence as the theorem statement.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The $p=2$ template exists in the parent and can be generalized.
- Pure `Nat.choose`/`Finset.sum` combinatorics, no analysis.
- Main effort is careful reindexing for general $p$.

**Estimated Effort**:
- Exploration: a few hours
- If tractable: 2–3 days
- If hard: unknown (if the general-$p$ reindex resists)

## References

### Mathlib
- `Mathlib.Combinatorics.Choose.Basic` — `Nat.choose`, `Nat.choose_succ_succ`.
- `Mathlib.Data.Nat.Fib` — Fibonacci for the $p=2$ base case.

## Metadata

```yaml
tags:
  - combinatorics
  - binomial-coefficients
  - fibonacci
  - pascal-triangle
  - p-bonacci
related_proofs:
  - combinations-formula-oq-01-oq-01
  - combinations-formula-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
