# Problem: Multiplicative Closed Form for the Divisor-Count Function τ(n)

**Slug**: sum-of-divisors-oq-06-oq-01
**Created**: 2026-07-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\tau(n) = \#\{d : d \mid n\} = \prod_{p \mid n} \bigl(v_p(n) + 1\bigr),
\qquad\text{in particular}\qquad \tau(p^a) = a + 1 .
$$

Here $v_p(n)$ is the $p$-adic valuation (the exponent of the prime $p$ in the
factorization of $n$), and the product ranges over the prime factors of $n$.

### Plain Language

The number-of-divisors function $\tau(n)$ counts how many positive integers
divide $n$. This problem asks for a fully machine-checked proof of its standard
closed form: $\tau$ is multiplicative, and on a prime power $p^a$ it takes the
value $a + 1$, so for a general $n = \prod p_i^{a_i}$ we get
$\tau(n) = \prod (a_i + 1)$. The special case $\tau(p^a) = a+1$ should be
derived explicitly.

### Why This Matters

This is the multiplicative backbone underneath the parent gallery entry
("The Number of Divisors τ(n) is Odd ⟺ n is a Perfect Square"): once the
product form is available, the perfect-square parity criterion, abundancy
computations, and the σ-function evaluations all follow as corollaries. It is a
reusable, citable identity for the number-theory portion of the gallery.

## Known Results

### What's Already Proven

- Parent entry `sum-of-divisors-oq-06`: τ(n) odd ⟺ n is a perfect square.
- Mathlib `Nat.card_divisors`: `n ≠ 0 → n.divisors.card = n.factorization.prod (fun _ k => k + 1)`.
- Mathlib `Nat.Coprime.card_divisors_mul`: multiplicativity of the divisor count.
- Mathlib `Nat.ArithmeticFunction.sigma` / `sigma_zero_apply`: σ₀ = τ.

### What's Still Open

- Packaging the identity as a standalone, self-contained gallery theorem
  (statement over `n.primeFactors` / `n.factorization`) with the `τ(pᵃ)=a+1`
  corollary spelled out, rather than leaving it implicit inside Mathlib.

### Our Goal

Produce a self-contained Lean entry stating and proving
`τ(n) = ∏_{p ∈ n.primeFactors} (n.factorization p + 1)` for `n ≥ 1`, plus the
prime-power corollary `τ(pᵃ) = a + 1`, verified with 0 sorries / 0 axioms.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sum-of-divisors-oq-06 | Parent; parity criterion follows from this product form | factorization, parity |
| sum-of-divisors (family) | σ and abundancy identities reuse the same multiplicative template | ArithmeticFunction, multiplicativity |

## Initial Thoughts

### Potential Approaches

1. **Direct via `Nat.card_divisors`**: the closed form is essentially a
   restatement of `Nat.card_divisors`; the work is rephrasing
   `n.factorization.prod` as a product over `n.primeFactors` of
   `n.factorization p + 1` and proving `τ(pᵃ) = a + 1` from
   `Nat.divisors_prime_pow` / `Nat.card_divisors`.
   - Why it might work: Mathlib already carries the hard content.
   - Risk: Finsupp.prod ↔ Finset.prod bookkeeping.

2. **From multiplicativity + prime powers**: prove τ multiplicative via
   `Nat.Coprime.card_divisors_mul`, evaluate on prime powers, then use
   `Nat.multiplicative_factorization` to assemble the product.
   - Why it might work: mirrors the classical textbook proof.
   - Risk: more moving parts than approach 1.

### Key Difficulties

- Translating between `Finsupp.prod` over `n.factorization` and `Finset.prod`
  over `n.primeFactors`.
- Handling the `n = 0` / `n = 1` edge cases cleanly.

### What Would a Proof Need?

- Key lemma: `τ(pᵃ) = a + 1` (via `Nat.divisors_prime_pow`).
- Key lemma: multiplicativity of `τ` on coprime arguments.
- Assembly: `Nat.multiplicative_factorization` or direct `Nat.card_divisors`.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The core identity is already in Mathlib (`Nat.card_divisors`); this is mostly
  a packaging + corollary-derivation exercise.
- Similar multiplicative-function entries already exist in the gallery.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Mathlib
- `Mathlib.NumberTheory.Divisors` — `Nat.card_divisors`, `Nat.divisors_prime_pow`
- `Mathlib.NumberTheory.ArithmeticFunction` — `sigma`, `sigma_zero_apply`, multiplicativity
- `Nat.Coprime.card_divisors_mul`, `Nat.multiplicative_factorization`

## Metadata

```yaml
tags:
  - number-theory
  - divisor-function
  - arithmetic-functions
  - multiplicative
  - factorization
related_proofs:
  - sum-of-divisors-oq-06
difficulty: low
source: gallery-gap
created: 2026-07-05
```

**Significance**: 6/10
**Tractability**: 7/10
