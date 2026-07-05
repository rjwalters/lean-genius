# Problem: Alternating harmonic conditional-convergence cautionary lemma

**Slug**: basel-problem-oq-10-oq-03
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For the alternating harmonic series $\sum_{n\ge 1} \frac{(-1)^{n+1}}{n}$:

$$
\lim_{N\to\infty}\sum_{n=1}^{N}\frac{(-1)^{n+1}}{n} = \ln 2,
\qquad\text{while}\qquad
\sum_{n}\frac{(-1)^{n+1}}{n}\ \text{(as an unordered \texttt{tsum}) is \emph{not} unconditionally summable.}
$$

### Plain Language

The parent `basel-problem-oq-10` records a cautionary "ordered limit ≠ tsum" pair for a
conditionally convergent series. This OQ asks for the **analogous pair** for the
alternating harmonic series: its ordered partial sums converge to `ln 2`, but the family
is not summable (`Summable` fails), so Mathlib's `tsum` does not equal `ln 2`. Package the
distinction as a reusable lemma capturing the conditional-convergence pitfall.

### Why This Matters

Conditional convergence is a classic trap: `∑ (-1)^{n+1}/n = ln 2` holds only as an
*ordered* limit, and Riemann rearrangement means the unordered `tsum` is ill-behaved.
A reusable lemma pins down exactly what Mathlib can and cannot say, preventing incorrect
`tsum` claims elsewhere in the gallery.

## Known Results

### What's Already Proven

- Parent `basel-problem-oq-10`: the cautionary ordered-limit-vs-tsum pattern for a
  conditionally convergent series.
- Mathlib: `Real.tendsto_sum_range_alternating_harmonic` / log-series results giving the
  ordered limit `ln 2`; `Real.not_summable_one_div_nat` and sign-variant summability lemmas.

### Our Goal

State and prove: (a) the ordered partial sums tend to `ln 2`; (b) `¬ Summable (fun n => (-1)^(n+1)/n)`,
hence the unordered `tsum` cannot be asserted equal to `ln 2`. Unify into one lemma.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| basel-problem-oq-10 | parent; same cautionary pattern | ordered limit vs tsum |

## Initial Thoughts

### Potential Approaches

1. **Reuse Mathlib**: obtain the `ln 2` ordered limit from the Mathlib alternating/log
   series API; obtain non-summability from `¬ Summable (1/n)` plus a comparison on `|aₙ|`.
   - Risk: locating the exact Mathlib lemma name for the `ln 2` ordered limit.

## Tractability Assessment

**Difficulty**: Medium

**Justification**: Both halves have Mathlib support (Leibniz `ln 2` series; harmonic
non-summability). Assembly and clean statement are the main work.

## References

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Log.Deriv` (log series), `Mathlib.Analysis.PSeries`
  (non-summability of the harmonic series).

## Metadata

```yaml
tags:
  - analysis
  - infinite-series
  - conditional-convergence
  - leibniz-formula
related_proofs:
  - basel-problem-oq-10
difficulty: medium
source: gallery-gap
created: 2026-07-01
```

**Significance**: 5/10
**Tractability**: 6/10
