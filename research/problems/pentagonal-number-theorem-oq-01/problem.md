# Problem: Euler's Pentagonal Number Theorem

**Slug**: pentagonal-number-theorem-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: seeker-selected <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\prod_{n=1}^{\infty} (1 - x^n) \;=\; \sum_{k=-\infty}^{\infty} (-1)^k\, x^{k(3k-1)/2}
\;=\; 1 + \sum_{k=1}^{\infty} (-1)^k\left(x^{k(3k-1)/2} + x^{k(3k+1)/2}\right).
$$

The exponents $g_k = k(3k-1)/2$ are the *generalized pentagonal numbers*
$0,1,2,5,7,12,15,22,26,\dots$. Equivalently, as a recurrence for the partition function
$p(n)$:
$$
p(n) = \sum_{k\ge 1} (-1)^{k-1}\Bigl(p\bigl(n - \tfrac{k(3k-1)}{2}\bigr)
+ p\bigl(n - \tfrac{k(3k+1)}{2}\bigr)\Bigr).
$$

### Plain Language

Multiply out the infinite product $(1-x)(1-x^2)(1-x^3)\cdots$. Almost all the coefficients
cancel: the only surviving terms are $\pm 1$, sitting at the "pentagonal number" positions
$1, 2, 5, 7, 12, 15, \dots$, with a regular alternating sign pattern. Restated, it gives a
fast alternating-sum recurrence for the number of ways to write $n$ as a sum of positive
integers (the partition function).

### Why This Matters

Euler's pentagonal number theorem (1750s) is one of the foundational identities of the
theory of partitions and $q$-series. It is the prototype for the Jacobi triple product, it
gives the most efficient classical recurrence for computing $p(n)$, and it is the entry
point to modular forms and the combinatorics of partitions (Franklin's bijective proof is a
gem of combinatorial reasoning). It is a famous named theorem with no current gallery entry
and (to the seeker's knowledge) not formalized as a named result in Mathlib, making it a
substantial and rewarding formalization target.

## Known Results

### What's Already Proven

- Mathlib has `Nat.Partition`, the partition function, and `Finset`/`Multiset` combinatorics
  for working with partitions.
- Mathlib has `PowerSeries` / `MvPowerSeries` and formal-power-series products, plus
  `PowerSeries.coeff`, supporting the generating-function side of the identity.
- The Jacobi triple product is a known specialization route; if a triple-product identity is
  available or provable, the pentagonal theorem follows as the $q \mapsto$ specialization.

### What's Still Open

- No Lean formalization of the pentagonal number theorem exists in this gallery.
- Neither the generating-function identity nor the equivalent partition recurrence has been
  assembled here, and Franklin's involution has not been formalized in this repository.

### Our Goal

Formalize the pentagonal number theorem in one of two equivalent forms: (a) the formal
power series identity $\prod_n (1-x^n) = \sum_k (-1)^k x^{k(3k-1)/2}$ in
`PowerSeries ℤ`, or (b) the equivalent partition recurrence for $p(n)$. Prefer Franklin's
bijective/involution proof, reducing the coefficient of $x^N$ to a sign-reversing involution
on partitions into distinct parts.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| binomial-theorem | Generating-function / formal power series manipulation | `PowerSeries`, coefficients |
| stirling-formula | Asymptotics and combinatorial sums | analytic combinatorics |
| basel-problem | Infinite product / series identities | product–sum identities |

## Initial Thoughts

### Potential Approaches

1. **Franklin's involution** (recommended): interpret the coefficient of $x^N$ in
   $\prod (1-x^n)$ as a signed count of partitions of $N$ into *distinct* parts (sign =
   parity of the number of parts). Define Franklin's sign-reversing involution (move the
   smallest part / the rightmost staircase) which is defined except on the exceptional
   pentagonal configurations; the unpaired survivors give exactly $(-1)^k$ at $N = g_k$.
   - Why it might work: turns the identity into a finite combinatorial bijection per
     coefficient — well suited to `Finset`/involution lemmas (`Finset.sum_involution`).
   - Risk: precisely characterizing the exceptional (unpaired) cases and proving the
     involution is well-defined off them.

2. **Generating functions / Jacobi triple product**: prove or import the triple product and
   specialize, working entirely in `PowerSeries ℤ` with coefficient extraction.
   - Why it might work: avoids combinatorial case analysis if the triple product is available.
   - Risk: the triple product is itself unformalized here and may be as hard as the target.

### Key Difficulties

- Equating the product's coefficient with a signed partition count (distinct parts) inside
  Mathlib's `PowerSeries`/`Nat.Partition` APIs.
- Defining Franklin's involution and proving it is sign-reversing and fixed-point-free
  outside the pentagonal exceptions (`Finset.sum_involution`-style bookkeeping).

### What Would a Proof Need?

- Key lemma 1: $\mathrm{coeff}_N \prod_{n}(1-x^n) = \sum_{\lambda \vdash N,\ \mathrm{distinct}}
  (-1)^{\#\mathrm{parts}(\lambda)}$.
- Key lemma 2 (crux): a sign-reversing involution on distinct-part partitions of $N$ whose
  only fixed points occur at $N = k(3k\pm1)/2$, contributing $(-1)^k$.
- Technical requirements: `PowerSeries`, `PowerSeries.coeff`, `Nat.Partition`,
  `Finset.sum_involution`.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The combinatorial heart (Franklin's involution) is elementary but fiddly to formalize: the
  exceptional-case analysis and the product-to-signed-count translation are both substantial.
- Mathlib provides the building blocks (`PowerSeries`, `Nat.Partition`, involution-sum
  lemmas) but no named pentagonal/triple-product result to reuse.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1–2 weeks
- If hard: 3–5 weeks (if the involution's exceptional cases resist clean formalization)

## References

### Papers
- L. Euler, *Evolutio producti infiniti* (1750s) — original discovery of the identity.
- F. Franklin, *Sur le développement du produit infini* (1881) — the bijective involution proof.
- G. E. Andrews, *The Theory of Partitions* (1976) — modern treatment and the triple product.

### Online Resources
- Wikipedia, "Pentagonal number theorem" — statement, Franklin's proof, the recurrence.

### Mathlib
- `Mathlib.RingTheory.PowerSeries.Basic` — formal power series, `coeff`, products.
- `Mathlib.Combinatorics.Partition` / `Nat.Partition` — partitions of a natural number.
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum_involution` and signed-sum bookkeeping.

## Metadata

```yaml
tags:
  - combinatorics
  - partitions
  - q-series
  - generating-functions
related_proofs:
  - binomial-theorem
  - basel-problem
difficulty: hard
source: seeker-selected
created: 2026-06-16
```
