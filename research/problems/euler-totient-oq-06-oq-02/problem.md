# Problem: Characterizing When phi(n) Is Congruent to 2 mod 4

**Slug**: euler-totient-oq-06-oq-02
**Created**: 2026-07-02T01:25:36-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\varphi(n) \equiv 2 \pmod 4 \iff v_2(\varphi(n)) = 1,
$$
characterized by factorization: $n$ has at most one odd prime factor, that prime satisfies
$p \equiv 3 \pmod 4$ (so $v_2(p-1)=1$), and the $2$-part of $n$ contributes no extra factor of $2$
(i.e. $n = p^k$ or $n = 2 p^k$).

### Plain Language

Euler's totient $\varphi(n)$ is even for all $n>2$ (parent oq-06). We now ask a finer question:
when is $\varphi(n)$ divisible by $2$ but *not* by $4$? Since
$\varphi(n)=\prod_{p^k \| n} p^{k-1}(p-1)$, each odd prime factor contributes an even $p-1$, and the
power of $2$ dividing $n$ contributes too. We characterize exactly the $n$ for which the total power
of $2$ in $\varphi(n)$ is precisely $1$, i.e. $v_2(\varphi(n)) = 1$.

### Why This Matters

This is the mod-4 refinement of the parity theorem and the first nontrivial layer of the full
$2$-adic valuation formula for $\varphi$. It pins down the (rare) case where
$(\mathbb{Z}/n\mathbb{Z})^\times$ has a cyclic $2$-Sylow of order exactly $2$, and it is a clean,
decidable-on-factorization statement — a good stepping stone toward the general $v_2(\varphi)$
question (sibling oq-01) without needing its full machinery.

## Known Results

### What's Already Proven

- $\varphi(n)$ is even for $n>2$, odd exactly at $n\in\{1,2\}$ — parent `euler-totient-oq-06` (verified).
- Multiplicativity $\varphi(mn)=\varphi(m)\varphi(n)$ for coprime $m,n$ and $\varphi(p^k)=p^{k-1}(p-1)$ — Mathlib `Nat.totient`.
- `Nat.totient_prime_pow`, `Nat.totient_mul` (coprime case) in Mathlib.

### What's Still Open

- The exact mod-4 characterization / equivalently the $v_2(\varphi(n))=1$ criterion in Lean.
- Deriving it cleanly from the multiplicative $2$-adic valuation of $\varphi$.

### Our Goal

Prove the biconditional $\varphi(n)\equiv 2 \pmod 4 \iff v_2(\varphi(n))=1$ and characterize such $n$
by their factorization. Verify against small cases $n=3,4,6$ (where $\varphi=2$) and contrast with
$n=5,8,15,\dots$ (where $4\mid\varphi$).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| euler-totient-oq-06 | Direct parent: parity of $\varphi$, evenness witness $-1$ | multiplicativity, prime-power formula |
| euler-totient-oq-05-oq-02 | Sibling: Carmichael $\lambda$ least universal exponent | group structure of $(\mathbb{Z}/n)^\times$ |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Reduce to $v_2$ additivity via multiplicativity.
   - Why it might work: $v_2(\varphi(n)) = \sum_{p^k\|n} v_2(p^{k-1}(p-1))$; each odd prime gives $v_2(p-1)\ge 1$, so the sum is $1$ iff exactly one odd prime with $v_2(p-1)=1$ (i.e. $p\equiv 3 \pmod 4$) and the $2$-part contributes $0$.
   - Risk: assembling `Nat.factorization` sums and handling the $2$-part term $\varphi(2^a)=2^{a-1}$ carefully.

2. **Approach B**: Case analysis on $n = 2^a m$ with $m$ odd.
   - Why it might work: $\varphi(n)=\varphi(2^a)\varphi(m)$; enumerate small $a$ and reduce $m$ to its odd-prime structure.
   - Risk: many cases; must ensure exhaustiveness.

### Key Difficulties

- Handling the $2$-part $\varphi(2^a)$: $a=0,1$ give $v_2=0$, $a\ge 2$ gives $v_2=a-1\ge1$.
- Summing $2$-adic valuations over the prime factorization within Mathlib's `Nat.factorization` framework.

### What Would a Proof Need?

- Key lemma 1: $v_2(\varphi(n)) = \sum_{p \in n.\text{primeFactors}} v_2(\varphi(p^{k_p}))$ via multiplicativity.
- Key lemma 2: for odd prime $p$, $v_2(p^{k-1}(p-1)) = v_2(p-1)$, and $v_2(p-1)=1 \iff p\equiv 3\pmod4$.
- Technical requirements: `Nat.factorization`, `Nat.totient_prime_pow`, `padicValNat 2`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- [Reason for assessment] The statement reduces to additivity of $v_2$ over a finite factorization — mechanical once the multiplicative decomposition is set up.
- [Similar problems that have been solved] Parent oq-06 already handled the parity (mod 2) layer with the same $\varphi(p^k)$ formula.
- [Techniques available in Mathlib] `Nat.totient_mul`, `Nat.totient_prime_pow`, `padicValNat`, `Nat.factorization` support this directly.

**Estimated Effort**:
- Exploration: 0.5–1 day
- If tractable: 3–5 days
- If hard: unknown

## References

### Papers
- G. H. Hardy & E. M. Wright, "An Introduction to the Theory of Numbers" — totient formula and prime-power structure.

### Online Resources
- https://en.wikipedia.org/wiki/Euler%27s_totient_function — multiplicativity and prime-power values.

### Mathlib
- `Mathlib.Data.Nat.Totient` — `Nat.totient`, `Nat.totient_prime_pow`, `Nat.totient_mul`.

## Metadata

```yaml
tags:
  - number-theory
  - totient-function
  - congruence
related_proofs:
  - euler-totient-oq-06
  - euler-totient-oq-05-oq-02
difficulty: medium
source: gallery-gap
created: 2026-07-02T01:25:36-07:00
```

**Significance**: 5/10
**Tractability**: 6/10
