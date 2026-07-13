# Problem: Explicit error bound for the Leibniz approximation of π/4

**Slug**: basel-problem-oq-10-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For every $k \in \mathbb{N}$,
$$
\left| \sum_{i=0}^{k-1} \frac{(-1)^i}{2i+1} \;-\; \frac{\pi}{4} \right| \;\le\; \frac{1}{2k+1}.
$$

### Plain Language

The parent entry (`basel-problem-oq-10`) shows that Leibniz's series
$\sum_{i\ge0} \tfrac{(-1)^i}{2i+1} = \tfrac{\pi}{4}$ converges only conditionally. This leaf
**quantifies** that convergence: the $k$-th partial sum differs from $\pi/4$ by at most
$\tfrac{1}{2k+1}$, the standard alternating-series remainder bound, giving an explicit (and famously
slow) rate for approximating $\pi/4$.

### Why This Matters

The bound makes the conditional convergence concrete and is the canonical worked example of the
alternating-series estimation theorem: the tail of an alternating series with terms decreasing to $0$
is bounded by the first omitted term $\tfrac{1}{2(k)+1}$. It quantifies exactly *why* Leibniz's
series is useless for fast numerical computation of $\pi$.

### Why the bound is $1/(2k+1)$

The first omitted term after summing $i = 0,\dots,k-1$ is $\tfrac{(-1)^k}{2k+1}$, whose absolute
value is $\tfrac{1}{2k+1}$. The alternating-series estimate says the remainder is bounded in absolute
value by exactly this first dropped term.

## Known Results

### What's Already Proven

- Parent `basel-problem-oq-10`: Leibniz series $\sum (-1)^i/(2i+1) = \pi/4$ converges conditionally (verified).
- Mathlib: `Real.tendsto_sum_pi_div_four` (or the arctan/Leibniz `HasSum`), and alternating-series
  estimate lemmas (`Antitone`/`tendsto_zero` ⟹ remainder bound).

### What's Still Open

- The explicit partial-sum error bound $\le 1/(2k+1)$ (this entry).

### Our Goal

Prove $\bigl|\sum_{i<k}(-1)^i/(2i+1) - \pi/4\bigr| \le 1/(2k+1)$ by instantiating Mathlib's
alternating-series estimation theorem with $a_i = 1/(2i+1)$ (antitone, tending to $0$) and the
parent's identification of the limit as $\pi/4$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| basel-problem-oq-10 | Direct parent; Leibniz series = π/4, conditional | arctan series, conditional convergence |
| basel-problem-oq-09-oq-01 | Sibling cluster; alternating zeta values | HasSum, parity split |
| basel-problem-oq-13 | Cousin; λ(4) odd-power sum | HasSum |

## Initial Thoughts

### Potential Approaches

1. **Apply the alternating-series estimation theorem**: with $a_i = \tfrac{1}{2i+1}$ antitone and
   $a_i \to 0$, Mathlib bounds the remainder $|S - S_k|$ by $a_k = \tfrac{1}{2k+1}$. Combine with the
   parent's limit value $S = \pi/4$.
   - Why it might work: Mathlib has the alternating-series bound; the antitonicity and limit-zero of
     $1/(2i+1)$ are routine `norm_num`/`gcongr` facts.
   - Risk: matching the exact statement form of Mathlib's alternating bound lemma (which partial-sum
     convention, `Finset.range` vs `∑'` tail) and aligning indices ($2k+1$ vs first-dropped-term).

### Key Difficulties

- Locating and matching the precise Mathlib alternating-series remainder lemma and its index/sign
  conventions; converting between the tail sum and the partial-sum error.

### What Would a Proof Need?

- Key lemma 1: $a_i = 1/(2i+1)$ is antitone and tends to $0$.
- Key lemma 2: alternating-series remainder bound $|S - S_k| \le a_k$ (Mathlib).
- Key lemma 3: parent's $S = \pi/4$.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The limit value is inherited from the verified parent; the remaining work is applying a standard
  Mathlib alternating-series estimate to an explicit antitone sequence.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Mathlib
- `Mathlib.Analysis.SpecificLimits.Basic` / alternating-series estimation lemmas.
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv` — arctan/Leibniz series for π/4.

## Metadata

```yaml
tags:
  - analysis
  - alternating-series
  - pi
  - error-bounds
related_proofs:
  - basel-problem-oq-10
  - basel-problem-oq-09-oq-01
  - basel-problem-oq-13
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
