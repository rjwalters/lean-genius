# Problem: Newton's Generalized Binomial Coefficient Identity (Negative Binomial Theorem)

**Slug**: stars-and-bars-weak-compositions-oq-01-oq-02
**Status**: Active
**Source**: proof-suggestion (open question from `stars-and-bars-weak-compositions-oq-01`)

## Problem Statement

### Formal Statement

Prove Newton's generalized binomial coefficient identity, in Mathlib's formal-power-series setting:

$$
(-1)^n \binom{-k}{n} = \binom{n+k-1}{n},
$$

where $\binom{-k}{n} = \frac{(-k)(-k-1)\cdots(-k-n+1)}{n!}$ is the generalized (Newton) binomial
coefficient. Connect it to the coefficient formula for $1/(1-X)^k$:

$$
[X^n]\,(1-X)^{-k} = \binom{n+k-1}{n},
$$

i.e. relate it to Mathlib's `PowerSeries.coeff_invOneSubPow_eq_choose`, giving the "negative
binomial theorem" reading of the same coefficients that the parent counted combinatorially.

### Plain Language

The parent showed the generating function for weak compositions is $1/(1-X)^k$. This asks to prove
the algebraic identity linking Newton's *negative* binomial coefficient $\binom{-k}{n}$ to the
*positive* stars-and-bars count $\binom{n+k-1}{n}$ — the two are equal up to sign $(-1)^n$.

### Why This Matters

It closes the loop between the combinatorial count (weak compositions) and the analytic expansion
of $(1-X)^{-k}$, making explicit that stars-and-bars *is* the negative binomial theorem.

## Known Results

### What's Already Proven

- Generating function $\sum_n \#\{\text{weak comps}\}\,X^n = (1-X)^{-k}$ — parent `stars-and-bars-weak-compositions-oq-01`.
- Mathlib `PowerSeries.coeff_invOneSubPow_eq_choose` and `Ring.choose` / `Nat.choose` API.

### Our Goal

Prove $(-1)^n \binom{-k}{n} = \binom{n+k-1}{n}$ and wire it to `coeff_invOneSubPow_eq_choose`,
0 axioms, 0 sorries.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| stars-and-bars-weak-compositions-oq-01 | Parent: gen. function $1/(1-X)^k$ | power series, generating functions |
| combinations-formula-* | Binomial coefficient manipulation | `Nat.choose`, absorption |

## Initial Thoughts

### Potential Approaches

1. **Falling-factorial expansion.** Expand $\binom{-k}{n}$ as a product, factor out $(-1)^n$, and
   match against $\binom{n+k-1}{n}$ via `Nat.ascFactorial` / `Ring.choose` lemmas.
2. **Coefficient route.** Compute $[X^n](1-X)^{-k}$ two ways (Newton expansion vs Mathlib's
   `coeff_invOneSubPow_eq_choose`) and equate.

### Key Difficulties

- Bridging `Ring.choose` (generalized) with `Nat.choose` (natural), and sign bookkeeping.
- Ensuring the power-series coefficient lemma matches the chosen indexing convention.
