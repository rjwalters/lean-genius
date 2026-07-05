# Problem: Odd-n vanishing of ∑ (−1)^k C(n,k)² via the k↦n−k involution

**Slug**: binomial-theorem-oq-06-oq-01-oq-02
**Created**: 2026-07-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For every **odd** natural number $n$,
$$
\sum_{k=0}^{n} (-1)^k \binom{n}{k}^2 = 0 .
$$

### Plain Language

The alternating sum of the squares of the binomial coefficients in row $n$ of
Pascal's triangle is zero whenever $n$ is odd. Prove it **directly** by the
sign-reversing involution $k \mapsto n-k$, independently of the
generating-function / Vandermonde route used elsewhere in the gallery, and
compare the two proofs.

### Why This Matters

The general closed form is $\sum_{k=0}^n (-1)^k \binom{n}{k}^2 = (-1)^{n/2}\binom{n}{n/2}$
for even $n$ and $0$ for odd $n$. The odd case has a clean combinatorial
explanation: the map $k \mapsto n-k$ pairs each term with its negative. Making
this bijective argument formal is a good showcase of `Finset.sum_involution`
and complements the algebraic (coefficient-extraction) proof.

## Known Results

### What's Already Proven

- Parent entry `binomial-theorem-oq-06-oq-01` — establishes the identity via the
  generating-function route ($[x^n](1-x)^n(1+x)^n$).
- Mathlib: `Nat.choose_symm` ($\binom{n}{k}=\binom{n}{n-k}$), `Finset.sum_involution`,
  `Finset.sum_ninvolution`.

### Our Goal

Give the involution proof: on $\{0,\dots,n\}$ the map $k\mapsto n-k$ is a
fixed-point-free involution when $n$ is odd (a fixed point would need $2k=n$,
impossible for odd $n$), it preserves $\binom{n}{k}^2$, and it flips the sign
$(-1)^k$ because $(-1)^{n-k} = (-1)^n(-1)^{-k} = -(-1)^k$. Hence the terms cancel
in pairs and the sum is $0$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| binomial-theorem-oq-06-oq-01 | parent; generating-function proof of the same identity | coefficient extraction |
| binomial-theorem | binomial coefficient API and identities | algebra |

## Initial Thoughts

### Potential Approaches

1. **Sign-reversing involution** (target): apply `Finset.sum_involution` with
   $g(k)=n-k$ on `Finset.range (n+1)`, showing each summand cancels its image.
   - Why it might work: no fixed points for odd $n$; $\binom{n}{k}^2$ symmetric.
   - Risk: bookkeeping of the $(-1)^{n-k}=-(-1)^k$ sign over `ℤ`; index-shift lemmas.

2. **Reduce to Vandermonde**: $\sum_k(-1)^k\binom{n}{k}^2 = [\text{coeff}]$ of
   $(1-x^2)^n$, which vanishes at odd degree.
   - Why: leverages existing algebra; but that is the route to be avoided/compared.

### What Would a Proof Need?

- Work over `ℤ` (signed sum).
- Fixed-point-free-ness of $k\mapsto n-k$ on `range (n+1)` for odd $n$.
- Sign lemma: `(-1)^(n-k) = -(-1)^k` for odd `n`, `k ≤ n`.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**: Elementary finite-sum identity; the involution is explicit and
Mathlib's `Finset.sum_involution` is designed for exactly this pattern. The only
fiddly part is the sign algebra. Estimated exploration: hours.

## References

### Mathlib
- `Finset.sum_involution` / `Finset.sum_ninvolution` — pairing-cancellation sums.
- `Nat.choose_symm`, `Nat.choose_symm_diff` — binomial symmetry.
- `Int.alternating_sum_range_choose` — related alternating binomial sum.

## Metadata

```yaml
tags:
  - combinatorics
  - binomial-coefficients
  - alternating-sums
  - involution
related_proofs:
  - binomial-theorem-oq-06-oq-01
  - binomial-theorem
difficulty: low
source: gallery-gap
created: 2026-07-05
```

**Significance**: 5/10
**Tractability**: 7/10
