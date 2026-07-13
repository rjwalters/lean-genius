# Problem: Taylor Series Convergence for sin and cos on all of ℝ

**Slug**: mean-value-theorem-oq-02-oq-01-oq-02
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent establishes Taylor remainder estimates converting derivative control to
function-value control, and proves convergence of the exponential Taylor series.
This leaf asks for the analogous result for the trigonometric functions, where the
uniform derivative bound is globally $M = 1$:

$$
\left\lvert \sin x - \sum_{k=0}^{n-1} \frac{(-1)^{k}}{(2k+1)!}\,x^{2k+1} \right\rvert
\;\le\; \frac{|x|^{n}}{n!} \xrightarrow[n\to\infty]{} 0
\quad\text{for every } x \in \mathbb{R},
$$

and likewise for $\cos$. Concretely: prove `sin_taylor_tendsto` and
`cos_taylor_tendsto` — the Taylor partial sums converge to $\sin$ / $\cos$ on all
of $\mathbb{R}$ — directly from the parent's `taylorPolynomial_tendsto` using the
global bound $\lvert \sin^{(n)} \rvert, \lvert \cos^{(n)} \rvert \le 1$.

### Plain Language

Every derivative of sine and cosine is again $\pm\sin$ or $\pm\cos$, so they are all
bounded by 1 everywhere. The parent already shows that a uniform bound $M$ on all
derivatives forces the Taylor series to converge; plugging in $M = 1$ gives global
convergence on the whole real line, with no interval restriction.

### Why This Matters

Sine/cosine are the cleanest instance of the parent's general convergence theorem
(the exp case needs $M$ growing with the interval; trig needs none). It closes the
trig branch of the parent's open questions.

## Known Results

### What's Already Proven

- `mean-value-theorem-oq-02-oq-01` (verified) — Taylor remainder estimates + exp convergence.
- Mathlib: `Real.sin`, `Real.cos`, iterated-derivative lemmas, `taylor_mean_remainder`.

### What's Still Open

- The trig convergence statements (this problem).

### Our Goal

Instantiate the parent's `taylorPolynomial_tendsto` with $M = 1$ for sin and cos.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| mean-value-theorem-oq-02-oq-01 | direct parent | Taylor remainder, derivative→value control |

## Initial Thoughts

### Potential Approaches

1. **Reuse parent theorem**: supply the global derivative bound $M=1$ and a tendsto
   of $|x|^n/n!$ to 0.
   - Why it might work: the parent already did the hard analytic work.
   - Risk: matching Mathlib's iterated-derivative form for sin/cos.

### Key Difficulties

- Expressing $\sin^{(n)}$ uniformly bounded by 1 in Mathlib's API.

### What Would a Proof Need?

- Bound: `‖iteratedDeriv n sin‖ ≤ 1` (and cos).
- Squeeze: $|x|^n/n! \to 0$ (Mathlib).

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The parent did the analysis; this is instantiation + a uniform bound lemma.
- Mathlib has factorial-decay and trig-derivative lemmas.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv` — trig derivatives.
- `Mathlib.Analysis.SpecificLimits.Basic` — `|x|^n / n! → 0`.

## Metadata

```yaml
tags:
  - analysis
  - calculus
  - taylor-series
related_proofs:
  - mean-value-theorem-oq-02-oq-01
difficulty: low
source: gallery-gap
created: 2026-06-24
```
