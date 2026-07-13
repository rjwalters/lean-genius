# Problem: The q-Binomial Theorem as a Polynomial Identity

**Slug**: combinations-formula-oq-03-oq-02
**Created**: 2026-07-02
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Over $\mathbb{Z}[q]$ (or any `CommRing`), prove the q-analog of the binomial theorem as
a polynomial identity in the variable $x$:

$$
\prod_{i=0}^{n-1} \bigl(1 + q^{i} x\bigr)
\;=\;
\sum_{k=0}^{n} \binom{n}{k}_{q}\, q^{\binom{k}{2}}\, x^{k},
\qquad \binom{k}{2} = \tfrac{k(k-1)}{2},
$$

where $\binom{n}{k}_q = $ `qBinom n k` is the Gaussian binomial coefficient from the
parent entry.

### Plain Language

The parent entry defines the q-binomial coefficients `qBinom` and proves the q-Pascal
recurrence / q-absorption. This child assembles those into the q-binomial theorem: the
finite product $\prod (1+q^i x)$ expands with q-binomial coefficients weighted by
$q^{k(k-1)/2}$. It is the exact q-deformation of $(1+x)^n = \sum \binom nk x^k$.

### Why This Matters

The q-binomial theorem is the foundational identity of q-hypergeometric series and
q-calculus; it underlies partition generating functions and the Rogers–Ramanujan circle.
Formalizing it in Lean turns the parent's `qBinom` definitions into a genuinely useful
algebraic tool.

## Known Results

### What's Already Proven

- Parent `combinations-formula-oq-03`: `qBinom` definition, `qBinom_absorption`, q-Pascal recurrence.
- Mathlib `Polynomial` / `MvPolynomial` ring structure; `Finset.prod_range_succ`, `Finset.sum_range_succ`.
- Ordinary binomial theorem `add_pow` / `Commute.add_pow` as the $q=1$ shadow.

### What's Still Open (in this child)

- The polynomial identity itself in $\mathbb{Z}[q][x]$ (or `Polynomial R` with `R = ℤ[q]`).
- A clean induction on $n$ using the q-Pascal recurrence to shift the product by one factor.

### Our Goal

Prove the q-binomial theorem by induction on $n$: multiplying the degree-$(n-1)$ identity
by $(1 + q^{\,n-1} x)$ and matching coefficients via the q-Pascal recurrence
$\binom nk_q = \binom{n-1}{k}_q + q^{\,n-k}\binom{n-1}{k-1}_q$ (or the dual form), tracking
the $q^{\binom k2}$ weights.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| combinations-formula-oq-03 | parent: qBinom + q-Pascal | q-analog recurrences |
| binomial-theorem-oq-06 | $q=1$ shadow, convolution identities | `add_pow`, Vandermonde |
| combinations-formula-oq-02-oq-03 | Catalan/Segner recurrence (sibling family) | induction on product |

## Initial Thoughts

### Potential Approaches

1. **Induction on $n$ via q-Pascal**: base $n=0$ gives $1 = \binom00_q x^0$. Step: multiply
   IH by $(1+q^{n-1}x)$; the two contributions to the $x^k$ coefficient are
   $\binom{n-1}{k}_q q^{\binom k2}$ and $q^{n-1}\cdot \binom{n-1}{k-1}_q q^{\binom{k-1}2}$;
   check $q^{n-1+\binom{k-1}2} = q^{\binom k2}\cdot q^{\,n-k}$ and apply q-Pascal.
   - Why it might work: the exponent arithmetic $\binom{k-1}2 + (n-1) = \binom k2 + (n-k)$
     is an `omega`/`ring`-checkable identity; q-Pascal is already proven upstream.
   - Risk: choosing the q-Pascal variant that matches the product's factor order.

2. **Work in `Polynomial (Polynomial ℤ)`** treating $q$ as the inner variable and $x$ as outer,
   or in `MvPolynomial (Fin 2) ℤ`.
   - Why it might work: keeps coefficient comparison honest.
   - Risk: `MvPolynomial` coefficient extraction is more verbose than univariate.

### Key Difficulties

- Matching the $q^{\binom k2}$ weights across the recurrence step (exponent bookkeeping).
- Choosing a representation (`Polynomial (Polynomial ℤ)` vs `MvPolynomial`) that keeps
  coefficient comparison tractable.

### What Would a Proof Need?

- q-Pascal recurrence in the exact orientation used by the product (import from parent).
- Exponent lemma $\binom{k-1}{2} + (n-1) = \binom{k}{2} + (n-k)$ for $1 \le k \le n$.
- Coefficient-extraction API (`Polynomial.coeff_mul`, `Finset.sum_range_succ`).

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- `qBinom` and the q-Pascal recurrence already exist in the parent — this is assembly.
- Structurally parallel to the ordinary binomial theorem induction, which is standard.

**Estimated Effort**:
- Exploration: hours
- If tractable: 2–4 days (coefficient bookkeeping)

## References

### Papers
- Andrews, *The Theory of Partitions* (1976), Ch. 3 — q-binomial theorem.

### Mathlib
- `Polynomial` coeff/mul API; `Finset.prod_range_succ`, `Finset.sum_range_succ`.
- Parent `qBinom` and q-Pascal lemmas (imported).

## Metadata

```yaml
tags:
  - combinatorics
  - q-analog
  - polynomial-identity
  - binomial-theorem
related_proofs:
  - combinations-formula-oq-03
  - binomial-theorem-oq-06
difficulty: medium
source: gallery-gap
created: 2026-07-02
```

**Significance**: 7/10
**Tractability**: 6/10
