# Problem: Infinitely Many Primes ≡ 1 (mod 4) — Elementary Proof

**Slug**: infinitude-primes-4k3-oq-03
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{There are infinitely many primes } p \equiv 1 \pmod{4}
$$

Elementary proof: For any finite set $\{p_1, \ldots, p_k\}$ of primes $\equiv 1 \pmod 4$, the number $N = (2p_1 \cdots p_k)^2 + 1$ has a prime factor $\equiv 1 \pmod 4$, giving a contradiction.

### Plain Language

The gallery proves infinitely many primes $\equiv 3 \pmod 4$ (a straightforward Euclid-style argument). Primes $\equiv 1 \pmod 4$ are harder: the standard proof uses Fermat's theorem that $-1$ is a quadratic residue mod $p$ if and only if $p \equiv 1 \pmod 4$.

**Elementary argument**: Let $P = 2p_1 \cdots p_k$ where $p_i \equiv 1 \pmod 4$. Set $N = P^2 + 1$. Since $N \equiv 1 \pmod 4$, all its prime factors are $\equiv 1$ or $\equiv 3 \pmod 4$. A prime $q \mid N$ satisfies $q \mid P^2 + 1$, so $P^2 \equiv -1 \pmod q$, meaning $-1$ is a quadratic residue mod $q$, so $q \equiv 1 \pmod 4$. But $q \nmid P$ (since $q \mid P^2 + 1$ and $\gcd(P, P^2+1) = 1$), so $q \notin \{p_1,\ldots,p_k\}$.

### Why This Matters

- Classic elementary number theory argument using Fermat's theorem on quadratic residues
- Important precursor to Dirichlet's theorem (which gives the much stronger density result)
- The connection between $p \equiv 1 \pmod 4$ and $-1$ being a QR mod $p$ is fundamental
- Formalizes a piece of algebraic number theory (quadratic reciprocity context) in Lean

## Known Results

### What's Already Proven

- Gallery: infinitude-primes-4k3 proves infinitely many primes $\equiv 3 \pmod 4$
- Mathlib: `Nat.Prime`, `Nat.Coprime`, quadratic residue basics
- Mathlib: `ZMod.isUnit_prime_iff_not_dvd`, modular arithmetic
- Fermat's theorem: if $p$ is an odd prime and $p \mid a^2 + 1$, then $p \equiv 1 \pmod 4$ (equivalent to $(-1|p) = 1$)

### What's Still Open

- Lean formalization of: if $p \mid a^2 + 1$ then $p \equiv 1 \pmod 4$
- The infinite descent argument in Lean

### Our Goal

Prove: `theorem infinitely_many_primes_one_mod_four : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p % 4 = 1) → ∃ q, q.Prime ∧ q % 4 = 1 ∧ q ∉ S`

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| infinitude-primes-4k3 | Direct predecessor | Infinitely many ≡ 3 mod 4 |
| elementary-quadratic-reciprocity | Key tool | Legendre symbol properties |
| eulers-formula | Context | Primes in Gaussian integers |

## Initial Thoughts

### Potential Approaches

1. **Direct N = P² + 1 argument**
   - Let $P = 2 \cdot \prod_{p_i \in S, p_i \equiv 1 \bmod 4} p_i$
   - $N = P^2 + 1 > 1$ so $N$ has a prime factor $q$
   - $q \mid P^2 + 1$ implies $q \nmid P$ (else $q \mid 1$), so $q \notin S$
   - Key lemma needed: $q \mid a^2 + 1 \Rightarrow q \equiv 1 \pmod 4$
   - This key lemma: $a^2 \equiv -1 \pmod q$ means $-1$ is a QR mod $q$, which requires $q \equiv 1 \pmod 4$ by Fermat's theorem
   - Why it might work: elementary, all steps finitary
   - Risk: proving the key lemma about QR in Lean

2. **Via ZMod quadratic residues in Mathlib**
   - `ZMod.isSquare_neg_one_iff` or similar in Mathlib
   - If $a^2 = -1$ in $ZMod q$, then the order of $a$ is 4, so 4 divides $q - 1$
   - Why it might work: Mathlib has group order theory
   - Risk: finding the right Mathlib lemma

### Key Difficulties

- The key lemma: $p \mid a^2 + 1 \Rightarrow p \equiv 1 \pmod 4$
  - Proof: $(a \cdot 2^{-1})^2 \equiv -1/4 \pmod p$? No, need ord$_p(a) = 4$
  - Actually: $a^4 \equiv 1 \pmod p$ and $a^2 \equiv -1 \not\equiv 1$, so ord($a$) = 4
  - Since ord($a$) | $p-1$, we get $4 \mid p-1$, i.e., $p \equiv 1 \pmod 4$
  - In Lean: `ZMod.orderOf_dvd_card_sub_one` or `ZMod.pow_card_sub_one_eq_one`

### What Would a Proof Need?

- `ZMod.orderOf_dvd_card_sub_one` : for prime $p$ and $a \not\equiv 0$, ord($a$) | $p-1$
- `Nat.dvd_of_mul_dvd_mul` or similar for the divisibility conclusion
- `Finset.prod_primes_pos` for constructing $P$

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Elementary argument but requires Mathlib's ZMod infrastructure
- The key lemma about element order in (ℤ/pℤ)* is the main technical hurdle
- Mathlib has the required group theory; finding the right lemma names is the challenge
- Comparable to similar elementary number theory formalizations in the gallery

**Estimated Effort**:
- Exploration: 2-3 hours (finding Mathlib lemmas)
- Implementation: 1-2 days
- Total: medium difficulty

## References

### Papers
- Hardy and Wright, "An Introduction to the Theory of Numbers" §4.2 — elementary proof
- Ireland and Rosen, "A Classical Introduction to Modern Number Theory" Chapter 5

### Mathlib
- `Mathlib.NumberTheory.LegendreSymbol.Basic` — quadratic residues
- `Mathlib.NumberTheory.ArithmeticFunction` — arithmetic functions
- `Mathlib.GroupTheory.OrderOfElement` — element orders in groups

## Metadata

```yaml
tags:
  - number-theory
  - elementary
  - modular-arithmetic
  - quadratic-residues
  - seeker-selected
related_proofs:
  - infinitude-primes-4k3
  - elementary-quadratic-reciprocity
difficulty: medium
source: gallery-gap
created: 2026-04-21
```
