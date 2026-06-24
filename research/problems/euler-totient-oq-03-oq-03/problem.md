# Problem: Exact GCD–Totient Identity φ(a)φ(b)·gcd(a,b) = φ(ab)·φ(gcd(a,b))

**Slug**: euler-totient-oq-03-oq-03
**Created**: 2026-06-24
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\forall a,b\in\mathbb{N}_{>0}:\quad \varphi(ab)\,\varphi(\gcd(a,b)) = \varphi(a)\,\varphi(b)\,\gcd(a,b),\quad\text{equivalently}\quad \varphi(ab)=\varphi(a)\,\varphi(b)\,\frac{\gcd(a,b)}{\varphi(\gcd(a,b))}.
$$

### Plain Language

Euler's totient is multiplicative only on coprime arguments: φ(ab) = φ(a)φ(b) when gcd(a,b)=1. The parent records the super-multiplicativity inequality φ(ab) ≥ φ(a)φ(b). This open question sharpens it to an exact identity for ALL a,b: φ(ab) = φ(a)φ(b)·d/φ(d) where d = gcd(a,b). Cross-multiplying to avoid division gives the clean Nat identity φ(ab)·φ(gcd(a,b)) = φ(a)·φ(b)·gcd(a,b). The goal is to formalize this exact GCD–totient identity, recovering the coprime multiplicativity (d=1) as a special case.

### Why This Matters

- Promotes a one-sided inequality in the gallery to an exact closed form, the genuinely sharp statement of how φ interacts with non-coprime products.
- The identity φ(ab)φ(d)=φ(a)φ(b)d is a standard but frequently-cited number-theory lemma worth a clean verified formalization.
- Mathlib has Nat.totient, Nat.Coprime.totient_mul, and the divisor/gcd API; the proof reduces to multiplicativity on prime-power valuations or a known totient_mul_of_... lemma.

## Known Results

### What's Already Proven

- Parent euler-totient-oq-03 (verified, 0-axiom): super-multiplicativity φ(ab) ≥ φ(a)φ(b).
- Mathlib: Nat.Coprime.totient_mul (φ(ab)=φ(a)φ(b) when coprime), Nat.totient_prime_pow.
- Classical: φ(ab) = φ(a)φ(b)·gcd(a,b)/φ(gcd(a,b)) (Apostol, Introduction to Analytic Number Theory, Thm 2.5 ex.).

### What's Still Open

- Q1: Prove the cross-multiplied Nat identity Nat.totient (a*b) * Nat.totient (Nat.gcd a b) = Nat.totient a * Nat.totient b * Nat.gcd a b for a,b>0.
- Q2: Derive the division form φ(ab)=φ(a)φ(b)·d/φ(d) and confirm φ(d) ∣ φ(a)φ(b)d so the division is exact.
- Q3: Recover Nat.Coprime.totient_mul (d=1 ⇒ φ(d)=1, gcd=1) as a one-line corollary.

### Our Goal

Prove the exact GCD–totient identity φ(ab)·φ(gcd(a,b)) = φ(a)·φ(b)·gcd(a,b) for positive a,b, verified/0-axiom, with coprime multiplicativity as a corollary.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| euler-totient-oq-03 | parent open question | source of this extension |
| euler-totient | ancestor in the same family | shared definitions and lemmas |

## Initial Thoughts

### Potential Approaches

1. **Prime-power valuation / multiplicative reduction**: Reduce to prime powers: for each prime p, compare v_p on both sides using φ(p^k)=p^k−p^{k-1}; the identity is multiplicative so it suffices on prime powers a=p^i, b=p^j.
   - Risk: Setting up the per-prime reduction cleanly in Mathlib (ArithmeticFunction.IsMultiplicative machinery) and the prime-power base computation.
2. **Direct via Nat.totient_mul / gcd*lcm**: Combine φ on a, b, gcd, lcm with a*b = gcd*lcm and any existing Mathlib totient product lemma; verify with the gcd–lcm factorization.
   - Risk: Whether a sufficiently general totient_mul lemma exists at v4.26 or it must be assembled from prime-power pieces.

### Key Difficulties

- Mathlib's totient multiplicativity is stated for coprime args; the non-coprime correction needs prime-power bookkeeping.
- Keeping everything in ℕ (the d/φ(d) factor is integral but division in ℕ needs the divisibility witness).

### What Would a Proof Need?

- φ(p^k) closed form and IsMultiplicative of φ.
- Cross-multiplied (division-free) ℕ statement.
- gcd·lcm = a·b factorization if using the lcm route.

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- Highest tractability of this batch: a well-known textbook identity with all Mathlib pieces present.
- Many euler-totient OQ siblings are verified/0-axiom (prime-power growth, coprimality of totient families).
- Prime-power reduction is a routine, well-trodden Mathlib pattern for multiplicative functions.

**Estimated Effort**:
- Exploration: hours
- If tractable: days

## References

### Papers
- T. M. Apostol, Introduction to Analytic Number Theory (1976) Ch. 2 — totient identities.
- G. H. Hardy, E. M. Wright, An Introduction to the Theory of Numbers (1938) §16 — Euler's function.

### Online Resources
- https://en.wikipedia.org/wiki/Euler%27s_totient_function#Divisor_sum
- https://oeis.org/A000010

### Mathlib
- Mathlib.NumberTheory.Divisors / Mathlib.Data.Nat.Totient — Nat.totient, Nat.Coprime.totient_mul
- Mathlib.NumberTheory.ArithmeticFunction — IsMultiplicative
- Mathlib.Data.Nat.GCD.Basic — Nat.gcd, gcd_mul_lcm

## Metadata

```yaml
tags:
  - seeker-selected
  - number-theory
  - totient
  - multiplicative-functions
  - gcd
  - product-formula
related_proofs:
  - euler-totient
  - euler-totient-oq-03
difficulty: low
source: proof-suggestion
created: 2026-06-24
```
