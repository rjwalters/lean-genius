# Problem: SLLN necessity for $L^p$ convergence ($p>1$)

**Slug**: laws-of-large-numbers-oq-01-oq-01-oq-02
**Created**: 2026-07-04T12:34:40-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{If } X_i \text{ i.i.d. and } \frac{1}{n}\sum_{i=1}^n X_i \xrightarrow{L^p} c \ (p>1),
\quad\text{does it follow that } \mathbb{E}\,|X_1|^p < \infty ?
$$

### Plain Language

Kolmogorov's strong law says i.i.d. variables with finite mean satisfy
$(1/n)\sum X_i \to \mathbb{E}X$ almost surely, and the *necessity* direction shows that
a.s. convergence of the averages forces $\mathbb{E}|X| < \infty$. This problem asks
whether the analogous necessity holds for convergence in $L^p$ ($p>1$): if the sample
means converge to $c$ in $p$-th mean, must the $p$-th moment $\mathbb{E}|X|^p$ be finite?

### Why This Matters

The gallery entry `laws-of-large-numbers-oq-01-oq-01` formalizes the necessity direction of
Kolmogorov's SLLN (a.s. convergence $\Rightarrow$ finite mean). Extending necessity to the
$L^p$ setting sharpens the moment/convergence dictionary and would produce Mathlib lemmas
about $L^p$ convergence of empirical means that are currently absent.

## Known Results

### What's Already Proven

- SLLN necessity (a.s.): $(1/n)\sum X_i$ converges a.s. $\Rightarrow \mathbb{E}|X| < \infty$ — formalized in the parent entry.
- Marcinkiewicz–Zygmund SLLN — for $1 \le p < 2$, $\mathbb{E}|X|^p < \infty$ characterizes a.s. convergence of $n^{-1/p}\sum(X_i - c)$.

### What's Still Open (for this formalization)

- A clean statement and proof that $L^p$ convergence of the averages implies $\mathbb{E}|X|^p < \infty$.
- Whether the converse (moment $\Rightarrow$ $L^p$ convergence, via uniform integrability of $|\bar X_n|^p$) belongs in the same file.

### Our Goal

Formalize: if $\bar X_n \to c$ in $L^p$ with $p>1$ and $X_i$ i.i.d., then $\mathbb{E}|X_1|^p < \infty$.
Start from $p=2$ (variance) as a warm-up before general $p$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| laws-of-large-numbers-oq-01-oq-01 | parent SLLN-necessity entry | Borel–Cantelli, truncation |
| central-limit-theorem-oq-02-oq-04 | moment conditions and normalized sums | characteristic functions, moments |

## Initial Thoughts

### Potential Approaches

1. **Symmetrization + lower bound on $\mathbb{E}|X|^p$**: if $\mathbb{E}|X|^p = \infty$, use
   independence to force $\mathbb{E}|\bar X_n - c|^p$ bounded away from $0$, contradicting $L^p$ convergence.
   - Why it might work: mirrors the a.s. necessity truncation argument.
   - Risk: controlling cross terms in $\mathbb{E}|\bar X_n|^p$ for general $p$.

2. **$p=2$ variance route first**: $L^2$ convergence of $\bar X_n$ with i.i.d. terms directly
   pins $\operatorname{Var}(X) < \infty$ by orthogonality; generalize afterwards.
   - Why it might work: $L^2$ is Hilbert-space clean and well-supported in Mathlib.
   - Risk: the $p \ne 2$ generalization needs different (non-orthogonal) estimates.

### Key Difficulties

- Mathlib's $L^p$ / `MeasureTheory.Lp` API and i.i.d. `iIndepFun` interplay.
- Passing from a moment lower bound to a contradiction with the convergence hypothesis.

### What Would a Proof Need?

- Key lemma 1: for i.i.d. $X_i$, a lower bound on $\mathbb{E}|\bar X_n - c|^p$ when $\mathbb{E}|X|^p = \infty$.
- Key lemma 2: $L^p$ convergence $\Rightarrow$ $\mathbb{E}|\bar X_n - c|^p \to 0$ (definitional).
- Technical requirements: truncation/symmetrization lemmas in the `MeasureTheory` namespace.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The $p=2$ case is tractable and a natural first deliverable.
- General $p$ needs Marcinkiewicz–Zygmund-style estimates not yet in Mathlib.
- Requires fluency with the `MeasureTheory.Lp` and independence APIs.

**Estimated Effort**:
- Exploration: 2-3 days
- If tractable ($p=2$): 1-2 weeks
- If hard (general $p$): unknown

## References

### Papers
- J. Marcinkiewicz, A. Zygmund, "Sur les fonctions indépendantes" (1937) — moment/convergence equivalence.

### Online Resources
- https://en.wikipedia.org/wiki/Law_of_large_numbers — statements and moment hypotheses.

### Mathlib
- `Mathlib.MeasureTheory.Function.LpSpace` — $L^p$ norms and convergence.
- `Mathlib.Probability.IdentDistrib` / `ProbabilityTheory.iIndepFun` — i.i.d. structure.

## Metadata

```yaml
tags:
  - probability
  - measure-theory
  - law-of-large-numbers
  - borel-cantelli
  - convergence
related_proofs:
  - laws-of-large-numbers-oq-01-oq-01
  - central-limit-theorem-oq-02-oq-04
difficulty: high
source: proof-suggestion
created: 2026-07-04T12:34:40-07:00
```

**Significance**: 6/10
**Tractability**: 5/10
