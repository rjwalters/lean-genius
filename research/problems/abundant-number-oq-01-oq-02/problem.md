# Problem: Smallest Odd Abundant Number Is 945

**Slug**: abundant-number-oq-01-oq-02
**Created**: 2026-06-18
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\sigma(945) > 2 \cdot 945 \quad\text{and}\quad \forall\, n < 945,\ \big(n \text{ odd} \Rightarrow \sigma(n) \le 2n\big),
$$

where $\sigma(n) = \sum_{d \mid n} d$ is the sum-of-divisors function. Equivalently, $945$ is the least odd $n$ with $\sigma(n) > 2n$ (the least odd abundant number).

### Plain Language

A number is *abundant* when the sum of its proper divisors exceeds the number itself (equivalently $\sigma(n) > 2n$). Even abundant numbers are common — $12$ is the smallest. Odd abundant numbers are far rarer; the smallest is $945 = 3^3 \cdot 5 \cdot 7$. We want a machine-checked proof that $945$ is abundant and that no smaller odd number is.

### Why This Matters

This extends the gallery's "12 is the smallest abundant number" result to the odd case, a classic and frequently-cited fact in elementary number theory. The interesting formalization challenge is keeping the bounded search over $n < 945$ kernel-reducible (hence axiom-free) without a `native_decide` that would pull in `Lean.ofReduceBool`.

## Known Results

### What's Already Proven

- `abundant-number-oq-01` ("Abundant Numbers: 12 Is Smallest, and There Are Infinitely Many") — gives the abundance definition, the $\sigma$ machinery, and the smallest-even result.
- Mathlib `Nat.sigma` / `Nat.ArithmeticFunction.sigma` provides the divisor-sum function and basic identities (multiplicativity, prime-power values).

### What's Still Open

- The odd-case minimality statement is not in the gallery.
- A kernel-friendly decision procedure for $\sigma(n) \le 2n$ over odd $n < 945$ that avoids `native_decide`.

### Our Goal

Prove `945` is the smallest odd abundant number as a standalone, axiom-free Lean theorem, reusing the parent's $\sigma$ infrastructure. The minimality half is a finite check over odd $n \in \{1, 3, \dots, 943\}$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| abundant-number-oq-01 | Same $\sigma$ definitions, smallest-even analogue | divisor-sum, decidability, infinitude |
| Mathlib `Nat.sigma` lemmas | Prime-power and multiplicative evaluation of $\sigma$ | arithmetic functions |

## Initial Thoughts

### Potential Approaches

1. **Approach A — direct bounded decision**: state minimality as `∀ n, n < 945 → Odd n → σ n ≤ 2*n` and discharge it with a kernel-reducible `Decidable` instance over the bounded range. Risk: naive `Nat.sigma` reduction over ~470 odd values may be slow in the kernel; may need a fast divisor-sum via factorization.
2. **Approach B — Finset.range filter**: convert the universal bound into a `Finset.range 945` computation with `Finset.filter Odd`, prove the predicate by `decide` on a `List`/`Finset` Boolean, again keeping it kernel-reducible.

### Key Difficulties

- Avoiding `native_decide` while keeping the check fast enough for the kernel (the abundant-number parent notes this tension explicitly).
- Efficient $\sigma$: evaluating $\sigma$ by trial division for each $n < 945$ vs. via prime factorization.

### What Would a Proof Need?

- A kernel-reducible computation of $\sigma(n)$ for $n < 945$.
- The single positive witness $\sigma(945) = 1920 > 1890$.
- A finite, decidable sweep establishing no smaller odd $n$ is abundant.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical content is elementary and the witness ($945$) is known.
- Solved analogue exists (smallest even abundant number) with reusable machinery.
- The only real risk is kernel-reduction performance of the bounded sweep.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days
- If hard (kernel perf forces a custom fast $\sigma$): up to a week

## References

### Papers
- L. E. Dickson, *History of the Theory of Numbers, Vol. I* — classical treatment of abundant/perfect numbers.

### Online Resources
- OEIS A005231 (odd abundant numbers) — $945$ is the first term.

### Mathlib
- `Mathlib.NumberTheory.Divisors` / `Nat.sigma` — divisor sums.
- `Nat.ArithmeticFunction.sigma` — multiplicative structure for prime-power evaluation.

## Metadata

```yaml
tags:
  - number-theory
  - divisor-sum
  - abundant-numbers
  - decidability
related_proofs:
  - abundant-number-oq-01
difficulty: medium
source: proof-suggestion
created: 2026-06-18
```
