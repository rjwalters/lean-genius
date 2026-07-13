# Problem: Optimal Smoothness of Outer Functions in Kolmogorov Superposition

**Slug**: hilbert-13-oq-01
**Created**: 2026-07-03
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
f(x_1,\dots,x_n) = \sum_{q=0}^{2n} \Phi_q\!\left( \sum_{p=1}^{n} \psi_{q,p}(x_p) \right).
$$

Given the Kolmogorov–Arnold representation above, determine the optimal (largest guaranteed) smoothness class of the **outer** functions $\Phi_q$ when the input $f$ is itself smooth (e.g. $f \in C^k$ or $C^\infty$).

### Plain Language

Kolmogorov and Arnold (1956–57) showed every continuous function of $n$ variables is a finite superposition of continuous one-variable functions — a striking negative answer to Hilbert's 13th. But Vitushkin showed the *smooth* story is different: smoothness cannot in general be preserved. This question asks precisely how much smoothness the outer functions $\Phi_q$ can retain when $f$ is smooth: what is the best regularity class one can always achieve?

### Why This Matters

The gap between the continuous (representable) and smooth (obstructed) cases is the mathematical heart of Hilbert's 13th and underpins modern interest in Kolmogorov–Arnold networks. Pinning down the optimal outer-function smoothness sharpens Vitushkin's obstruction into a quantitative regularity theory.

## Known Results

### What's Already Proven

- Kolmogorov–Arnold superposition theorem: continuous representation with $2n+1$ outer functions — parent entry `hilbert-13`.
- Vitushkin: smooth functions are not in general representable with smooth components (obstruction result).

### What's Still Open

- The exact optimal smoothness class of the outer functions $\Phi_q$ for smooth input.
- Constructive / algorithmic bounds matching the obstruction.

### Our Goal

Formalize the statement of the optimal-smoothness question and the Vitushkin obstruction that upper-bounds achievable smoothness, establishing a rigorous framework in which the optimum can be stated and (for restricted cases) proven.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| hilbert-13 | Direct parent; supplies the superposition representation | Kolmogorov–Arnold theorem |

## Initial Thoughts

### Potential Approaches

1. **Obstruction-first**: formalize Vitushkin-type dimension/entropy counting to bound achievable outer smoothness from above.
   - Why it might work: converts smoothness loss into a counting inequality.
   - Risk: entropy arguments are analysis-heavy and thin in Mathlib.

2. **Low-dimensional model case**: fix $n = 2$ and a concrete smoothness scale, and analyze what regularity the outer functions can attain.
   - Why it might work: isolates the phenomenon in the smallest nontrivial case.
   - Risk: even $n = 2$ requires careful real-analysis infrastructure.

### Key Difficulties

- Formalizing quantitative smoothness classes ($C^k$, Hölder, Lipschitz) and their behavior under composition.
- Vitushkin's obstruction relies on metric-entropy estimates not yet in Mathlib.

### What Would a Proof Need?

- Key lemma 1: composition/smoothness-tracking lemmas for $\Phi_q \circ (\sum \psi_{q,p})$.
- Key lemma 2: an entropy or dimension obstruction bounding outer smoothness.
- Technical requirements: `ContDiff`, Hölder spaces, real analysis on $\mathbb{R}^n$.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full optimal-smoothness question is a genuine open problem in analysis.
- Mathlib has `ContDiff` and continuity infrastructure but limited metric-entropy tooling.
- A formal *statement* plus a restricted obstruction is a realistic first milestone.

**Estimated Effort**:
- Exploration: days
- If tractable: weeks
- If hard: unknown

## References

### Papers
- A. N. Kolmogorov (1957); V. I. Arnold (1957) — superposition representation.
- A. G. Vitushkin — obstruction to smooth superposition.

### Online Resources
- Hilbert's 13th problem overview — https://en.wikipedia.org/wiki/Hilbert%27s_thirteenth_problem

### Mathlib
- `ContDiff`, `ContDiffOn` — smoothness classes.
- `HolderWith` — Hölder-continuity estimates.

## Metadata

```yaml
tags:
  - analysis
  - superposition
  - kolmogorov-arnold
  - hilbert-problems
related_proofs:
  - hilbert-13
difficulty: high
source: proof-suggestion
created: 2026-07-03
```

**Significance**: 7/10
**Tractability**: 4/10
