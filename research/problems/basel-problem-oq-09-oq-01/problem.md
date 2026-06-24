# Problem: Parity Split of the Riemann Zeta — λ(2m)=(1−2⁻²ᵐ)ζ(2m), λ(4)=π⁴/96

**Slug**: basel-problem-oq-09-oq-01
**Created**: 2026-06-24T07:47:49-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For every integer $m \ge 1$, the odd-index Dirichlet lambda value equals a rational multiple of the even-index zeta value:

$$
\lambda(2m) \;=\; \sum_{k=0}^{\infty} \frac{1}{(2k+1)^{2m}} \;=\; \bigl(1 - 2^{-2m}\bigr)\,\zeta(2m).
$$

In particular, specializing at $m = 2$,

$$
\lambda(4) \;=\; \sum_{k=0}^{\infty} \frac{1}{(2k+1)^{4}} \;=\; \frac{15}{16}\,\zeta(4) \;=\; \frac{15}{16}\cdot\frac{\pi^4}{90} \;=\; \frac{\pi^4}{96}.
$$

### Plain Language

The full zeta sum $\zeta(2m)=\sum_{n\ge 1} n^{-2m}$ splits into its even-index and odd-index parts. The even-index part is $\sum_{n\ge 1}(2n)^{-2m}=2^{-2m}\zeta(2m)$, so the odd-index part (the lambda value) is exactly the remaining fraction $(1-2^{-2m})\zeta(2m)$. Applied to fourth powers, this turns the known closed form $\zeta(4)=\pi^4/90$ into the closed form $\sum 1/(2k+1)^4 = \pi^4/96$ — the fourth-power analogue of the parent's odd-square result $\sum 1/(2k+1)^2 = \pi^2/8$.

### Why This Matters

It abstracts the parent entry's ad-hoc even/odd manipulation into a clean, uniform parity-split identity valid at every even order $2m$, and connects the elementary "odd reciprocal powers" sums to Mathlib's machinery for the Riemann zeta function at even integers. It is the natural bridge from the order-2 case to the whole family $\lambda(4), \lambda(6), \dots$, and a stepping stone to the Dirichlet eta values (sibling entries oq-10..oq-14).

## Known Results

### What's Already Proven

- Parent `basel-problem-oq-09`: $\sum_{k} 1/(2k+1)^2 = \pi^2/8$ (the $m=1$ case), verified, 0-axiom.
- Mathlib `hasSum_zeta_four`: $\sum_{n\ge 1} 1/n^4 = \pi^4/90$.
- Mathlib `hasSum_zeta_two`: $\sum_{n\ge 1} 1/n^2 = \pi^2/6$.
- Mathlib summability/reindexing API for splitting a series over $\mathbb{N}$ into even and odd subsequences (`HasSum`, `Summable.even_add_odd`, reindexing by $n \mapsto 2n$, $n \mapsto 2n+1$).

### What's Still Open

- The general parity-split identity $\lambda(2m) = (1-2^{-2m})\zeta(2m)$ stated uniformly in $m$ (or at least the explicit $m=2$ instance $\lambda(4)=\pi^4/96$).

### Our Goal

Prove the $m=2$ instance $\lambda(4) = \pi^4/96$ rigorously from `hasSum_zeta_four` via the even/odd split, and, if convenient, state the general $\lambda(2m)=(1-2^{-2m})\zeta(2m)$ identity for an arbitrary even-power summable family. The general statement need only assume the relevant `HasSum`/`Summable` hypotheses already available in Mathlib for even integer arguments.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| basel-problem-oq-09 | parent — order-2 case $\sum 1/(2k+1)^2=\pi^2/8$ | even/odd split, `hasSum_zeta_two` |
| basel-problem (root) | $\zeta(2)=\pi^2/6$ | Fourier / Parseval |

## Initial Thoughts

### Potential Approaches

1. **Even/odd `HasSum` split**: Write $\zeta(2m) = (\text{even part}) + (\text{odd part})$ using `Summable.even_add_odd` (or `HasSum` reindexing). The even part is $\sum (2n)^{-2m} = 2^{-2m}\zeta(2m)$ by pulling out $2^{-2m}$, leaving the odd part $= (1-2^{-2m})\zeta(2m)$.
   - Why it might work: this is exactly the parent's order-2 strategy; only the exponent changes.
   - Risk: index bookkeeping (Mathlib's odd-index family is $2k+1$ starting at $k=0$; matching to the $n$-indexed even part).

2. **Direct from `hasSum_zeta_four`**: pull the factor $2^{-4}=1/16$ out of the even subsum, then `1 - 1/16 = 15/16` and arithmetic to $\pi^4/96$.
   - Why it might work: fully concrete; `field_simp`/`ring`/`norm_num` close the rational arithmetic.
   - Risk: none significant.

### Key Difficulties

- Reindexing the even subsequence and extracting the scalar $2^{-2m}$ cleanly under `HasSum`.
- Keeping a general-$m$ statement honest (summability hypothesis must come from Mathlib for the even-power case).

### What Would a Proof Need?

- Key lemma 1: even/odd decomposition of an absolutely convergent series over $\mathbb{N}$.
- Key lemma 2: $\sum (2n)^{-s} = 2^{-s}\sum n^{-s}$ (scalar pull-out under `HasSum`).
- Technical: `hasSum_zeta_four`, rational arithmetic $15/16 \cdot 1/90 = 1/96$.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The parent already proved the order-2 instance with the identical strategy; this is a re-run at exponent 4 plus a uniform restatement.
- Mathlib supplies the needed zeta value (`hasSum_zeta_four`) and the even/odd `HasSum` API.
- No new analytic input is required — only reindexing and rational arithmetic.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Online Resources
- Dirichlet lambda function, $\lambda(s)=(1-2^{-s})\zeta(s)$ — standard identity.

### Mathlib
- `Mathlib.NumberTheory.ZetaValues` / `hasSum_zeta_four`, `hasSum_zeta_two` — even-integer zeta values.
- `Summable.even_add_odd`, `HasSum` reindexing — parity split.

## Metadata

```yaml
tags:
  - analysis
  - number-theory
  - zeta
  - basel
related_proofs:
  - basel-problem-oq-09
  - basel-problem
difficulty: medium
source: gallery-gap
created: 2026-06-24T07:47:49-07:00
```
