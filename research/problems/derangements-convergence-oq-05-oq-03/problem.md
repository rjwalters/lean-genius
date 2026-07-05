# Problem: Factorial Moments of the Fixed-Point Count Are All 1 (Poisson(1) Hallmark)

**Slug**: derangements-convergence-oq-05-oq-03
**Created**: 2026-07-02T01:25:36-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{For } X_n = \#\{\text{fixed points of a uniform } \sigma \in S_n\},\quad
\mathbb{E}\big[(X_n)_r\big] = \mathbb{E}\big[X_n(X_n-1)\cdots(X_n-r+1)\big] = 1 \quad (0 \le r \le n),
$$
$$
\text{hence } \mathbb{E}[X_n] = 1 \text{ and } \operatorname{Var}(X_n) = 1.
$$

### Plain Language

Pick a permutation of $\{1,\dots,n\}$ uniformly at random and count how many elements it fixes.
Call that count $X_n$. The $r$-th *factorial moment* is the expected value of the falling
product $X_n(X_n-1)\cdots(X_n-r+1)$. We want to show every factorial moment equals exactly $1$,
independent of $n$ (for $r \le n$). This is the algebraic signature of the Poisson(1) distribution,
and it immediately yields mean $1$ and variance $1$.

### Why This Matters

Matching *all* factorial moments to $1$ is the cleanest route to the Poisson(1) limit: it explains
*why* the fixed-point distribution converges to Poisson(1) (parent oq-05) rather than merely
asserting the pointwise limit. It also packages the classic "expected number of fixed points is 1"
fact into a full moment description, connecting derangement combinatorics to elementary probability.

## Known Results

### What's Already Proven

- $D_k(n) = \binom{n}{k} D(n-k)$, the exact count of permutations with $k$ fixed points — parent `derangements-convergence-oq-05` (verified).
- $D_k(n)/n! \to e^{-1}/k!$ (Poisson(1) pointwise limit) — parent `derangements-convergence-oq-05`.
- `Nat.card_fixedPoints` / `Equiv.Perm` fixed-point API and `Nat.derangements` count in Mathlib.

### What's Still Open

- The falling-factorial (factorial-moment) identity $\mathbb{E}[(X_n)_r] = 1$ in Lean.
- The corollaries $\mathbb{E}[X_n]=1$ and $\operatorname{Var}(X_n)=1$ derived from it.

### Our Goal

Prove $\mathbb{E}[(X_n)_r] = 1$ for $0 \le r \le n$ by the counting identity
$\sum_k (k)_r \binom{n}{k} D(n-k) = \binom{n}{r}(r)_r \cdot (n-r)! \cdot \tfrac{1}{(n-r)!}\cdots$
— concretely, count ordered $r$-tuples of fixed points: each ordered $r$-tuple of distinct points
is fixed by exactly $(n-r)!$ permutations, and there are $(n)_r$ such tuples, so
$\sum_\sigma (X_n(\sigma))_r = (n)_r (n-r)! = n!$, giving mean-1 factorial moments after dividing by $n!$.
Then specialize $r=1,2$ for mean and variance.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| derangements-convergence-oq-05 | Direct parent: supplies $D_k(n)=\binom{n}{k}D(n-k)$ and the Poisson limit | derangement counting, alternating-series bound |
| derangements-convergence-oq-04-oq-04 | Sibling on additive derangement recurrence | bijective counting |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Double-counting ordered $r$-tuples of fixed points.
   - Why it might work: $\sum_\sigma (X_n(\sigma))_r$ counts pairs $(\sigma, \text{ordered } r\text{-tuple of fixed points})$; fixing the tuple leaves $(n-r)!$ permutations, and there are $(n)_r$ tuples, so the sum is $(n)_r(n-r)! = n!$.
   - Risk: Formalizing "ordered $r$-tuple of fixed points" cleanly against Mathlib's `Equiv.Perm` fixed-point sets.

2. **Approach B**: Sum the exact counts $\sum_k (k)_r D_k(n) = \sum_k (k)_r \binom{n}{k} D(n-k)$ and simplify via the falling-factorial/binomial absorption $(k)_r\binom{n}{k} = (n)_r\binom{n-r}{k-r}$.
   - Why it might work: reduces to $\sum_j \binom{n-r}{j} D(n-r-j) = (n-r)!$, a known total-count identity.
   - Risk: index shifting $k \mapsto k-r$ and the derangement-sum identity need care.

### Key Difficulties

- Choosing the representation of $X_n$ (as `Finset.card` of fixed points vs. a random variable) that makes the falling factorial tractable.
- The absorption identity $(k)_r\binom{n}{k} = (n)_r\binom{n-r}{k-r}$ must be available or proved.

### What Would a Proof Need?

- Key lemma 1: $\sum_{j} \binom{m}{j} D(m-j) = m!$ (permutations partition by fixed-point set).
- Key lemma 2: falling-factorial absorption $(k)_r \binom{n}{k} = (n)_r \binom{n-r}{k-r}$.
- Technical requirements: Mathlib `Nat.descFactorial`, `Nat.choose` absorption, derangement count `Nat.derangements`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- [Reason for assessment] The double-counting argument is elementary and self-contained; the hardest part is index bookkeeping, not deep theory.
- [Similar problems that have been solved] Parent oq-05 and the oq-04-oq-04 bijective recurrence show this derangement API is well-trodden in the gallery.
- [Techniques available in Mathlib] `Nat.descFactorial`, `Nat.choose_mul_descFactorial`-style absorption, derangement counts, `Finset.sum` manipulation.

**Estimated Effort**:
- Exploration: 0.5–1 day
- If tractable: 2–4 days
- If hard: unknown

## References

### Papers
- P. Diaconis, "Group Representations in Probability and Statistics" (1988) — fixed-point counts and Poisson approximation via moments.

### Online Resources
- https://en.wikipedia.org/wiki/Factorial_moment — falling-factorial moments and the Poisson signature.

### Mathlib
- `Mathlib.Combinatorics.Derangements.Basic` — derangement counts $D(n)$ and `Nat.card` of fixed-point-free permutations.

## Metadata

```yaml
tags:
  - combinatorics
  - probability
  - derangements
related_proofs:
  - derangements-convergence-oq-05
  - derangements-convergence-oq-04-oq-04
difficulty: medium
source: gallery-gap
created: 2026-07-02T01:25:36-07:00
```

**Significance**: 5/10
**Tractability**: 7/10
