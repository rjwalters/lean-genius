# Problem: Möbius Companion — Aperiodic Necklaces, Lyndon Words, and Fermat

**Slug**: burnside-counting-oq-06-oq-02
**Created**: 2026-07-02
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
L_k(n) \;=\; \frac{1}{n}\sum_{d \mid n} \mu(d)\, k^{\,n/d}
$$

counts the aperiodic necklaces (equivalently, Lyndon words) of length $n$ over a
$k$-letter alphabet. In particular $L_k(n) \in \mathbb{Z}_{\ge 0}$, and at a prime
$p$ it specializes to $L_k(p) = \dfrac{k^p - k}{p}$, so that

$$
p \mid (k^p - k), \qquad\text{i.e.}\qquad k^p \equiv k \pmod p
$$

(Fermat's little theorem) falls out of the count being an integer.

### Plain Language

The parent entry counts *all* necklaces (colorings up to rotation) via Burnside's
lemma and a totient sum. This child proves the Möbius-inverse companion: the count
of necklaces with no rotational symmetry (aperiodic ones). Because that count is an
integer and equals $(k^p-k)/p$ at a prime $p$, we recover Fermat's little theorem
as a corollary of a combinatorial counting argument.

### Why This Matters

The pairing (totient count) $\leftrightarrow$ (Möbius count) is the classic
Möbius-inversion duality on the divisor lattice, and the Lyndon-word interpretation
connects to free Lie algebras and the necklace-polynomial identity. Deriving Fermat's
little theorem from a *counting* argument (rather than group theory) is a pedagogically
valued classical proof (the "necklace proof" of Fermat).

## Known Results

### What's Already Proven

- Parent `burnside-counting-oq-06`: totient necklace count $\frac1n\sum_{d\mid n}\varphi(d)k^{n/d}$.
- Mathlib `Nat.ArithmeticFunction.moebius`, `Nat.ArithmeticFunction.moebius_mul_coe_zeta` (Möbius inversion).
- Mathlib `Nat.sum_totient`, divisor-sum API `Nat.sum_divisors_*`.

### What's Still Open (in this child)

- A Lean statement and proof that $\sum_{d\mid n}\mu(d)k^{n/d}$ is divisible by $n$
  (equivalently $L_k(n)\in\mathbb{Z}$) — the necklace-count integrality.
- The prime specialization $L_k(p)=(k^p-k)/p$ and the resulting $k^p\equiv k\pmod p$.

### Our Goal

Prove integrality of the Möbius necklace sum and derive Fermat's little theorem
$k^p \equiv k \pmod p$ at prime $p$ as the clean corollary. Full combinatorial
Lyndon-word bijection is optional stretch; the arithmetic identity is the core target.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| burnside-counting-oq-06 | parent: totient necklace count | Burnside, divisor sums |
| euler-totient-* | Möbius/totient divisor-sum machinery | arithmetic functions |
| four-square-distribution-oq-06-* | divisor-sum + parity closed forms | `Nat.divisors` sums |

## Initial Thoughts

### Potential Approaches

1. **Direct integrality via Möbius inversion**: define $a(n)=k^n$; then
   $\sum_{d\mid n}\mu(d)k^{n/d}$ is the Möbius transform. Show $n \mid$ this sum by a
   group-action / orbit-counting argument (aperiodic words come in orbits of size exactly $n$).
   - Why it might work: Mathlib has the Möbius-inversion lemmas and `ZMod n` cyclic action.
   - Risk: formalizing "aperiodic ⇒ orbit size exactly $n$" may need custom combinatorics.

2. **Prime case first**: at $n=p$ prime, the sum is $k^p - k$ (only $d=1,p$),
   and `ZMod.pow_card` / `Finset.sum` over the free action gives $p \mid (k^p-k)$ directly.
   - Why it might work: Mathlib already has `ZMod.pow_card : a^p = a`.
   - Risk: makes Fermat trivial via Mathlib; value is the *necklace-count framing*, so keep the general $L_k(n)$ integrality as the headline.

### Key Difficulties

- Establishing integrality of $L_k(n)$ for composite $n$ (the orbit-size argument).
- Keeping the result distinct from Mathlib's `ZMod.pow_card` (frame via necklace counting).

### What Would a Proof Need?

- Möbius transform of $n\mapsto k^n$ and a divisibility lemma $n \mid \sum_{d\mid n}\mu(d)k^{n/d}$.
- The prime corollary and the congruence `k^p ≡ k [ZMOD p]`.

## Tractability Assessment

**Difficulty**: Medium (prime case Low)

**Justification**:
- Prime specialization is nearly immediate from Mathlib `ZMod.pow_card`.
- General integrality is a known, elementary orbit-counting fact; Mathlib has the Möbius API.
- Sibling `burnside-counting-oq-06-oq-01` handled the totient side successfully.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Papers
- N. G. de Bruijn / Moreau's necklace-counting formula (1872) — aperiodic necklace count.

### Mathlib
- `Nat.ArithmeticFunction.moebius`, Möbius inversion lemmas — the Möbius transform.
- `ZMod.pow_card` — Fermat's little theorem for the prime corollary.
- `Nat.divisors`, `Finset.sum_divisors` — divisor-sum manipulation.

## Metadata

```yaml
tags:
  - combinatorics
  - number-theory
  - mobius-inversion
  - necklaces
  - lyndon-words
related_proofs:
  - burnside-counting-oq-06
  - euler-totient
difficulty: medium
source: gallery-gap
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 7/10
