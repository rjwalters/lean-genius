# Problem: Carmichael's Function and Theorem

**Slug**: euler-totient-oq-01
**Created**: 2026-03-30
**Status**: Active
**Source**: gallery-extension (from euler-totient openQuestion #1)

## Problem Statement

### Formal Statement

$$
\lambda(n) = \text{lcm of orders of elements in } (\mathbb{Z}/n\mathbb{Z})^\times
$$
$$
\forall a,\, \gcd(a,n) = 1 \implies a^{\lambda(n)} \equiv 1 \pmod{n}
$$

### Plain Language

The Carmichael function $\lambda(n)$ gives the smallest positive exponent $m$ such that $a^m \equiv 1 \pmod{n}$ for all integers $a$ coprime to $n$. This refines Euler's theorem, which uses $\varphi(n)$ -- the Carmichael function always divides $\varphi(n)$ and is often strictly smaller.

### Why This Matters

- Carmichael's function is the true exponent of the multiplicative group $(\mathbb{Z}/n\mathbb{Z})^\times$
- Used in RSA (Carmichael's $\lambda$ gives tighter bounds than Euler's $\varphi$)
- Connects group theory (exponent vs order) to number theory

## Known Results

### What's Already Proven

- `euler-totient` gallery proof: $a^{\varphi(n)} \equiv 1 \pmod{n}$ -- fully verified, Mathlib-backed
- Mathlib has `ZMod.pow_totient` and `Nat.totient` infrastructure
- Mathlib has `orderOf` for group elements

### What's Still Open

- Defining $\lambda(n)$ in Lean and proving the universal exponent property
- The explicit formula: $\lambda(2^a) = 2^{a-2}$ for $a \geq 3$, $\lambda(p^a) = p^{a-1}(p-1)$ for odd primes
- $\lambda(\text{lcm}(m,n)) = \text{lcm}(\lambda(m), \lambda(n))$

### Our Goal

Formalize the Carmichael function $\lambda(n)$ and prove that $a^{\lambda(n)} \equiv 1 \pmod{n}$ for all $\gcd(a,n) = 1$, extending the euler-totient gallery proof.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| euler-totient | Parent proof, Euler's theorem | Mathlib ZMod, Lagrange's theorem |
| chinese-remainder-non-coprime | CRT for computing $\lambda$ | Chinese Remainder Theorem |
| primitive-roots | Cyclic group structure | Group generators, orders |

## Initial Thoughts

### Potential Approaches

1. **Group exponent approach**: Define $\lambda(n)$ as `Finset.lcm` of `orderOf` over all units
   - Why it might work: Direct definition using Mathlib group theory
   - Risk: May need infrastructure for `exponent` of finite groups

2. **Explicit formula approach**: Define via prime power formula and lcm
   - Why it might work: Concrete and computable
   - Risk: Needs casework for $n = 2^a$ special case

### Key Difficulties

- Mathlib may or may not have `Monoid.exponent` for finite groups
- The $\lambda(2^a) = 2^{a-2}$ formula needs careful casework

### What Would a Proof Need?

- Definition of Carmichael's $\lambda$ function
- Proof that $\lambda(n) \mid \varphi(n)$
- Proof that $\lambda(n)$ is the minimal universal exponent

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Euler's theorem infrastructure already exists in Mathlib
- Group exponent concepts may exist or be close
- Clear mathematical path from existing gallery proof

## References

### Mathlib
- `Mathlib.Data.ZMod.Basic` -- ZMod units and pow_totient
- `Mathlib.Data.Nat.Totient` -- Euler's totient function
- `Mathlib.GroupTheory.OrderOfElement` -- orderOf in groups

## Metadata

```yaml
tags:
  - number-theory
  - modular-arithmetic
  - group-theory
related_proofs:
  - euler-totient
  - chinese-remainder-non-coprime
  - primitive-roots
difficulty: medium
source: gallery-extension
created: 2026-03-30
```
