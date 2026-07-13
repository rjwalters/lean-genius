# Problem: Idempotents of ℤ/n via unitary divisors (CRT, 2^ω(n) count)

**Slug**: automorphic-number-oq-01-oq-02-oq-01-oq-02
**Created**: 2026-07-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $n = \prod_{i=1}^{\omega(n)} p_i^{e_i}$. Describe every idempotent of the ring
$\mathbb{Z}/n\mathbb{Z}$ (element $x$ with $x^2 = x$) **directly** in terms of the
unitary divisors of $n$, and give an effective enumeration establishing
$$
\#\{\,x \in \mathbb{Z}/n\mathbb{Z} : x^2 = x\,\} = 2^{\omega(n)},
$$
where $\omega(n)$ is the number of distinct prime factors of $n$.

### Plain Language

An element of $\mathbb{Z}/n$ is idempotent iff it looks like $0$ or $1$ modulo
each prime-power factor of $n$. By the Chinese Remainder Theorem these local
choices are independent, so idempotents biject with subsets of the prime factors
— equivalently with the **unitary divisors** $d \mid n$ with $\gcd(d, n/d)=1$.
There are $2^{\omega(n)}$ of them.

### Why This Matters

This is the ring-theoretic backbone of the automorphic-number entries: an
$n$-adic automorphic number is exactly an idempotent of $\mathbb{Z}/10^k$. A clean
general-modulus classification (not just prime-power exponents) closes the gap
left open by the parent entry and gives an effective enumeration.

## Known Results

### What's Already Proven

- Parent `automorphic-number-oq-01-oq-02-oq-01` — handles idempotents for
  prime-power-exponent moduli / the 10^k automorphic case.
- Standard: a finite product of **local** rings $\mathbb{Z}/p^e$ has exactly the two
  trivial idempotents $0, 1$ (local ring ⇒ no nontrivial idempotents).

### What's Still Open (our goal)

- Package the general modulus: via `ZMod.chineseRemainder`,
  $\mathbb{Z}/n \cong \prod_i \mathbb{Z}/p_i^{e_i}$; transport idempotency across the
  ring iso; idempotents of a product are componentwise idempotents; each factor
  contributes $\{0,1\}$; conclude a bijection with `Finset` of subsets of the
  prime factors and hence cardinality $2^{\omega(n)}$.
- Identify each idempotent with the unitary divisor $d = \prod_{i \in S} p_i^{e_i}$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| automorphic-number-oq-01-oq-02-oq-01 | parent; prime-power / 10^k idempotents | ZMod, CRT |
| automorphic-number | definition of automorphic numbers as idempotents | modular arithmetic |

## Initial Thoughts

### Potential Approaches

1. **CRT + local rings** (target): `ZMod.chineseRemainder` to split into
   prime-power factors; `IsLocalRing`/`ZMod` gives only $0,1$ idempotent per
   factor; product idempotents are componentwise; count $= 2^{\omega(n)}$.
   - Risk: assembling the counting bijection to `n.primeFactors.powerset`;
     matching the iso's `Pi` idempotents to unitary divisors.

2. **Direct Hensel/lifting**: solve $x^2 \equiv x$ mod each $p^e$ by uniqueness of
   idempotent lifts. More machinery; CRT route is cleaner.

### What Would a Proof Need?

- `ZMod.chineseRemainder` and its ring-iso transport of `IsIdempotentElem`.
- Idempotents of `∀ i, R i` are `fun i => (e i)` with each `e i` idempotent.
- Each `ZMod (p^e)` (local) has exactly two idempotents.
- `Nat.ArithmeticFunction.cardDistinctFactors` / `Nat.primeFactors.card` = ω(n).

## Tractability Assessment

**Difficulty**: Medium

**Justification**: Every ingredient is in Mathlib (`ZMod.chineseRemainder`,
idempotents, `Nat.primeFactors`). The work is in stitching the CRT iso to the
$2^{\omega(n)}$ count and the unitary-divisor description. No deep new theory.

## References

### Mathlib
- `ZMod.chineseRemainder` — $\mathbb{Z}/(m n) \cong \mathbb{Z}/m \times \mathbb{Z}/n$ for coprime.
- `IsIdempotentElem`, `IsLocalRing` — idempotent API; local ⇒ trivial idempotents.
- `Nat.primeFactors`, `Nat.factorization`, `Nat.ArithmeticFunction.cardDistinctFactors` — ω(n).

## Metadata

```yaml
tags:
  - number-theory
  - zmod
  - idempotents
  - chinese-remainder-theorem
related_proofs:
  - automorphic-number-oq-01-oq-02-oq-01
  - automorphic-number
difficulty: medium
source: gallery-gap
created: 2026-07-05
```

**Significance**: 5/10
**Tractability**: 6/10
