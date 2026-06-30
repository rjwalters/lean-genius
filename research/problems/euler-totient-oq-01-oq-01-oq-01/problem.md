# Problem: Carmichael Function as the lcm of Prime-Power Carmichael Values

**Slug**: euler-totient-oq-01-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For $n = \prod_i p_i^{k_i}$ with distinct primes $p_i$, the Carmichael function $\lambda$ satisfies

$$
\lambda(n) \;=\; \operatorname{lcm}_i \,\lambda\bigl(p_i^{k_i}\bigr),
$$

where $\lambda(m)$ is the exponent of the unit group $(\mathbb{Z}/m\mathbb{Z})^\times$ — the least $e \ge 1$ with $a^e \equiv 1 \pmod m$ for every $a$ coprime to $m$. This is the universal-exponent refinement of Euler's theorem: $\lambda(n) \mid \varphi(n)$, and $a^{\lambda(n)} \equiv 1 \pmod n$ for all $\gcd(a,n)=1$.

### Plain Language

Euler's theorem guarantees $a^{\varphi(n)} \equiv 1 \pmod n$ for $a$ coprime to $n$, but $\varphi(n)$ is usually not the *smallest* exponent that works for all such $a$. The smallest universal exponent is the Carmichael function $\lambda(n)$, the exponent of the group of units mod $n$. By the Chinese Remainder Theorem the unit group factors as a product over the prime powers dividing $n$, so its exponent is the lcm of the exponents of the factors: $\lambda(n) = \operatorname{lcm}_i \lambda(p_i^{k_i})$. This problem asks to complete the induction over the prime-power factorization and state that lcm identity as a single Lean theorem.

### Why This Matters

The Carmichael function is the sharp constant in Euler's theorem and the right tool for primality testing, the structure of $(\mathbb{Z}/n\mathbb{Z})^\times$, and Carmichael numbers. The multiplicative-via-lcm law is its defining structural property; formalizing it converts the parent entry's per-prime-power groundwork into the general multiplicative statement and gives downstream entries (group exponents, RSA-style order bounds) a clean lemma to cite.

## Known Results

### What's Already Proven

- Parent `euler-totient-oq-01-oq-01` (verified): prime-power / multiplicative groundwork for the totient and unit-group exponent.
- Mathlib: `ZMod.unitsEquivProdUnits`-style CRT decomposition of $(\mathbb{Z}/n)^\times$, `Monoid.exponent`, `Monoid.exponent_prod`, `Nat.lcm`, and `Nat.Coprime`.
- Classical: $\lambda$ is the exponent of $(\mathbb{Z}/n)^\times$; $\lambda(\prod p_i^{k_i}) = \operatorname{lcm}\lambda(p_i^{k_i})$ and $a^{\lambda(n)}\equiv 1$ for coprime $a$.

### What's Still Open

- A Lean definition of $\lambda(n) = \texttt{Monoid.exponent }(\mathbb{Z}/n)^\times$ (or an equivalent), and the theorem $\lambda(n) = \operatorname{lcm}_i \lambda(p_i^{k_i})$ via the CRT product decomposition.
- The corollary $\lambda(n) \mid \varphi(n)$ and the universal-exponent property $a^{\lambda(n)} \equiv 1 \pmod n$.

### Our Goal

Identify $\lambda$ with `Monoid.exponent` of the unit group, push the CRT factorization $(\mathbb{Z}/n)^\times \cong \prod_i (\mathbb{Z}/p_i^{k_i})^\times$ through `Monoid.exponent_prod` (exponent of a product $=$ lcm of exponents), and conclude the lcm identity by induction over the factorization.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| euler-totient-oq-01-oq-01 | Direct parent; prime-power totient/exponent groundwork | multiplicative number theory |
| euler-totient-oq-01 | Root entry; Euler's totient and its multiplicativity | $(\mathbb{Z}/n)^\times$, CRT |

## Initial Thoughts

### Potential Approaches

1. **Exponent-of-a-product via CRT.** Define $\lambda(n) = \texttt{Monoid.exponent }(\mathbb{Z}/n\mathbb{Z})^\times$, transport `Monoid.exponent` across the CRT group isomorphism, and apply `Monoid.exponent_prod` to get the lcm over coprime factors; induct on the factorization to reach individual prime powers.
   - Why it might work: Mathlib already has `Monoid.exponent_prod` (or `exponent` of a `Pi`/product) and the CRT unit-group equivalence; the lcm structure falls out directly.
   - Risk: the exact name/shape of the product-exponent lemma and threading the finite factorization (`Nat.factorization`) into a clean lcm.

2. **Direct order-theoretic lcm.** Prove $\lambda(n)$ is the lcm of the $\lambda(p_i^{k_i})$ by showing it is a common multiple (Euler per factor) that also divides any common universal exponent (CRT witness achieving each factor's exponent).
   - Why it might work: matches the textbook "least common universal exponent" argument; avoids depending on a specific product-exponent lemma name.
   - Risk: constructing the CRT witness element that realizes a given factor's exponent requires care.
