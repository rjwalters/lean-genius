# Problem: Bounded-Part Weak Compositions via Inclusion–Exclusion

**Slug**: stars-and-bars-weak-compositions-oq-01-oq-03
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Fix $k, r \ge 0$. Let $N_{\le r}(n, k)$ be the number of weak compositions of $n$ into $k$
ordered parts $(x_1, \dots, x_k)$ with $0 \le x_i \le r$ for every $i$, i.e.

$$
N_{\le r}(n, k) \;=\; \#\{(x_1,\dots,x_k) \in \mathbb{N}^k : \textstyle\sum_i x_i = n,\ x_i \le r\}.
$$

Prove the inclusion–exclusion closed form

$$
N_{\le r}(n, k) \;=\; \sum_{j=0}^{k} (-1)^j \binom{k}{j}\binom{n - j(r+1) + k - 1}{\,k-1\,},
$$

where $\binom{m}{k-1} = 0$ whenever $m < k-1$ (so only the terms with $j \le n/(r+1)$
contribute). The $r \to \infty$ (equivalently $r \ge n$) specialization must recover the
classical stars-and-bars count $\binom{n+k-1}{k-1}$ of the parent entry.

### Plain Language

Stars-and-bars counts the ways to distribute $n$ identical balls into $k$ labelled boxes:
$\binom{n+k-1}{k-1}$. This problem adds a *capacity*: no box may hold more than $r$ balls.
The answer is the same binomial count with an alternating correction that subtracts the
arrangements where one box overflows, adds back those where two overflow, and so on —
classic inclusion–exclusion. The task is a clean, machine-checked proof of that formula.

### Why This Matters

Capacity-constrained compositions are the combinatorial core of the coefficient extraction
$[x^n]\bigl(1 + x + \dots + x^r\bigr)^k = [x^n]\bigl(\tfrac{1-x^{r+1}}{1-x}\bigr)^k$, i.e.
coefficients of a truncated geometric / Gaussian-style generating function. They underlie
bounded dice-sum probabilities, contingency-table margins, and the $q\to 1$ limit of
Gaussian binomial coefficients. The parent `stars-and-bars-weak-compositions-oq-01`
formalizes the unbounded count; this entry supplies the bounded refinement, closing the
gap between the free and capacity-limited regimes with a single reusable lemma.

## Known Results

### What's Already Proven

- Unbounded weak-composition count $\binom{n+k-1}{k-1}$ — parent
  `stars-and-bars-weak-compositions-oq-01`.
- Mathlib has `Finset.Nat.antidiagonalTuple` / `Sym`-style counts and the binomial
  vanishing convention `Nat.choose_eq_zero_of_lt`.

### What's Still Open (for this entry)

- A formalized bounded count $N_{\le r}(n,k)$ with the alternating inclusion–exclusion sum.
- The consistency check that $r \ge n \Rightarrow N_{\le r}(n,k) = \binom{n+k-1}{k-1}$
  (only the $j=0$ term survives).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| stars-and-bars-weak-compositions-oq-01 | parent: unbounded count | stars-and-bars bijection |
| stars-and-bars-weak-compositions-oq-01-oq-01 | sibling: last-part recurrence | generating functions |
| inclusion-exclusion entries (if present) | the counting engine | sign-reversing involution |

## Initial Thoughts

### Potential Approaches

1. **Inclusion–exclusion over overflow sets.** For $S \subseteq \{1,\dots,k\}$, the
   compositions where every $i \in S$ has $x_i \ge r+1$ are counted (after shifting
   $x_i \mapsto x_i - (r+1)$) by $\binom{n - |S|(r+1) + k - 1}{k-1}$. Summing with signs
   over $|S| = j$ gives the formula.
   - Why it might work: the shift bijection is elementary and the binomial vanishing
     convention handles the range automatically.
   - Risk: bookkeeping the finite sum and the shift's non-negativity side conditions.

2. **Generating-function coefficient extraction.** Prove
   $[x^n]\bigl(\tfrac{1-x^{r+1}}{1-x}\bigr)^k$ equals the sum by expanding
   $(1-x^{r+1})^k$ with the binomial theorem and pairing with $\tfrac{1}{(1-x)^k}$'s
   stars-and-bars coefficients.
   - Why it might work: reuses the parent's negative-binomial expansion directly.
   - Risk: formal power-series coefficient manipulation in Lean is heavier than the
     combinatorial route.

### Key Difficulties

- Handling the vanishing convention `choose = 0` cleanly so the finite sum has fixed
  length $k+1$ regardless of $n, r$.
- The shift bijection's injectivity/surjectivity onto the "$\ge r+1$ on $S$" subset.

### What Would a Proof Need?

- Lemma: bijection between $\{x : \sum x = n,\ x_i \ge r+1\ \forall i\in S\}$ and weak
  compositions of $n - |S|(r+1)$ into $k$ parts.
- Lemma: `Finset.card` inclusion–exclusion (`Finset.card_biUnion` / sign-reversing form).
- `Nat.choose_eq_zero_of_lt` to kill out-of-range terms.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Pure finite combinatorics; no analysis.
- Inclusion–exclusion is available in Mathlib, and the shift bijection is standard.

**Estimated Effort**:
- Exploration: hours
- If tractable: 2–3 days

## References

### Mathlib
- `Mathlib.Combinatorics.Enumerative.Composition` — compositions.
- `Mathlib.Algebra.BigOperators.NatAntidiagonal` — tuple antidiagonals.
- `Mathlib.Data.Nat.Choose.Basic` — `Nat.choose`, vanishing lemmas.

### Online Resources
- Stanley, *Enumerative Combinatorics* Vol. 1, §1.2 (compositions, inclusion–exclusion).
- Coefficients of $\bigl(\frac{1-x^{r+1}}{1-x}\bigr)^k$ (truncated geometric powers).

## Metadata

```yaml
tags:
  - combinatorics
  - binomial-coefficients
  - inclusion-exclusion
  - stars-and-bars
related_proofs:
  - stars-and-bars-weak-compositions-oq-01
  - stars-and-bars-weak-compositions-oq-01-oq-01
difficulty: medium
source: gallery-gap
created: 2026-07-04
```

**Significance**: 5/10
**Tractability**: 7/10
