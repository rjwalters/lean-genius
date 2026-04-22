# Problem: Totient Product Formula φ(n) = n·∏(1-1/p) via Mathlib Prime Factorization

**Slug**: euler-totient-oq-02-oq-01
**Created**: 2026-04-21T21:53:58+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\varphi(n) = n \cdot \prod_{p \mid n, p \text{ prime}} \left(1 - \frac{1}{p}\right)
$$

Equivalently, using rational arithmetic:

$$
\varphi(n) = \prod_{p^k \| n} p^{k-1}(p-1)
$$

### Plain Language

Prove the totient product formula: φ(n) equals n multiplied by the product of (1 - 1/p) over all distinct prime divisors p of n. This expresses the totient function as a multiplicative function of the prime factorization.

For example: φ(12) = 12 · (1 - 1/2) · (1 - 1/3) = 12 · 1/2 · 2/3 = 4.

### Why This Matters

The product formula is the standard computational form for the totient. It:
- Shows φ is completely multiplicative over prime powers
- Connects to the Euler product for the Riemann zeta function: ζ(s)⁻¹ = ∏ₚ(1 - p⁻ˢ)
- Enables efficient computation: φ(n) = n · ∏ₚ|ₙ (p-1)/p
- Is the foundational identity for Euler's theorem a^φ(n) ≡ 1 (mod n)

## Known Results

### What's Already Proven

- `Nat.totient_prime_pow_succ`: φ(p^(k+1)) = p^k · (p-1) — in Mathlib
- `Nat.totient_mul_of_prime_of_dvd`, `Nat.totient_mul`: multiplicativity of φ — in Mathlib
- `euler-totient-oq-02`: multiplicative property φ(mn) = φ(m)·φ(n) for gcd(m,n)=1 — in gallery
- `Nat.factors` and `Nat.primeFactors`: prime factorization infrastructure — in Mathlib

### What's Still Open

- Direct formalization of φ(n) = n · ∏_{p|n} (p-1)/p as a Lean theorem
- Connecting `Nat.totient` to `Finset.prod` over `n.primeFactors`

### Our Goal

Prove `Nat.totient n = n * ∏ p in n.primeFactors, (p - 1) / p` (working in appropriate types, e.g., using `Nat.card_units_zmod_lt_eq_totient` or direct definitional unfolding), or the equivalent integer formulation `n.totient = n.primeFactors.prod (fun p => p - 1) * n.primeFactors.prod ... `.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| euler-totient | Parent proof: Euler's generalization of Fermat | ZMod.units, card |
| euler-totient-oq-02 | Direct parent: multiplicativity φ(mn) = φ(m)φ(n) | Finset.card, Nat.Coprime |
| euler-totient-oq-04 | Divisor sum n = ∑_{d|n} φ(d) | Finset.sum over divisors |
| fermats-little-theorem | Application of Euler's theorem | ZMod |

## Initial Thoughts

### Potential Approaches

1. **Via prime power factorization and multiplicativity**:
   - Factor n = ∏ p^k using `Nat.factorization`
   - Apply `Nat.totient_prime_pow_succ` to each prime power: φ(p^k) = p^(k-1)(p-1)
   - Combine using multiplicativity (`Nat.totient_mul`)
   - Why it might work: All pieces are in Mathlib
   - Risk: Bookkeeping of the finset product over `n.factorization.support`

2. **Via `Nat.ArithmeticFunction.totient` and the multiplicative structure**:
   - Use `Nat.ArithmeticFunction.IsMultiplicative.totient` from Mathlib
   - Apply the formula for multiplicative functions over prime powers
   - Risk: API surface for ArithmeticFunction may require more scaffolding

3. **Direct computation approach**:
   - Induction on prime factorization using `Nat.rec_on_prime_pow`
   - Might be simpler to set up but requires custom induction principle

### Key Difficulties

- Type mismatch: the product formula involves division, but `Nat.totient` returns `ℕ` (integer division or rational needed)
- Connecting `n.primeFactors` (a `Finset ℕ`) to `n.factorization.support`
- Ensuring the product over primes works correctly for n = 0 and n = 1

### What Would a Proof Need?

- Key lemma 1: `Nat.totient_prime_pow`: φ(p^k) = p^(k-1) * (p-1)
- Key lemma 2: Factorization of n as a product of prime powers
- Key lemma 3: Multiplicativity of totient over coprime prime powers
- Technical requirement: Working over `ℚ` or using integer arithmetic carefully

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- All building blocks are in Mathlib: `Nat.totient_prime_pow_succ`, `Nat.totient_mul`, `Nat.factorization`
- The proof is constructive: apply multiplicativity iteratively over prime factors
- Similar formulas (`card_units_zmod_lt_eq_totient`) already exist
- Mathlib 4 has strong `Finset.prod` infrastructure

**Estimated Effort**:
- Exploration: 2-4 hours
- If tractable: 1-2 days for full formalization

## References

### Papers
- Euler, L. "Theoremata arithmetica nova methodo demonstrata" (1763) — original proof

### Mathlib
- `Mathlib.Data.Nat.Totient` — φ definition and basic properties
- `Mathlib.Data.Nat.Factorization.Basic` — prime factorization
- `Mathlib.NumberTheory.ArithmeticFunction` — multiplicative function theory

## Metadata

```yaml
tags:
  - number-theory
  - totient-function
  - prime-factorization
  - multiplicative-functions
related_proofs:
  - euler-totient
  - euler-totient-oq-02
  - euler-totient-oq-04
difficulty: low
source: gallery-gap
created: 2026-04-21T21:53:58+02:00
```

**Significance**: 7/10
**Tractability**: 7/10
