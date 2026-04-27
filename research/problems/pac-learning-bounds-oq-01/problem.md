# Problem: VC Dimension of Threshold Classifiers on ℕ

## Statement

### Plain Language

The threshold hypothesis class on $\mathbb{N}$ is

$$H_{\mathrm{thr}} \;=\; \{x \mapsto (x < t) \;:\; t \in \mathbb{N}\}.$$

What is its VC dimension?

This is a concrete instance of the parent's open question OQ-01:
*"Can the VC dimension of specific hypothesis classes be computed in
Lean?"*

### Formal Statement

Show that the VC dimension of $H_{\mathrm{thr}}$ is exactly $1$. That is,
prove both:

1. **Lower bound.** Every singleton $\{a\}$ is shattered by
   $H_{\mathrm{thr}}$.
2. **Upper bound.** No two-point set $\{a, b\}$ with $a \neq b$ is
   shattered.

In Lean (`threshold_vcdim_bounds` in `PACLearningOQ01.lean`):

```lean
theorem threshold_vcdim_bounds :
    (∀ a, Shatters thresholdClassifiers {a}) ∧
    (∀ a b, a ≠ b → ¬ Shatters thresholdClassifiers {a, b})
```

## Classification

```yaml
tier: A
significance: 8
tractability: 5
tags:
  - learning-theory
  - combinatorics
  - vc-dimension
  - cs-math-bridge
  - completed
```

**Significance**: 8/10 (parent inheritance — concrete contribution to a
high-significance open question).
**Tractability**: 5/10 (already completed — proof is short and uses
standard Mathlib API).

## Why This Matters

1. **Canonical "smallest interesting" hypothesis class.** Threshold
   classifiers are the simplest nontrivial example of a PAC-learnable
   class over an infinite domain. VC dimension $1$ marks the exact
   boundary between trivial classes (constants, VC dim 0) and richer
   classes (intervals at VC dim 2, half-spaces at VC dim $d + 1$, etc.).

2. **Sample complexity is independent of the size of the domain.**
   Combining VC dim $= 1$ with the Fundamental Theorem of Statistical
   Learning gives explicit PAC sample complexity
   $m(\varepsilon, \delta) = O\bigl(\tfrac{1}{\varepsilon}(\log
   \tfrac{1}{\delta} + 1)\bigr)$ — independent of $|\mathbb{N}|$. This
   is the simplest example distinguishing PAC learnability from the
   trivial finite-class regime.

3. **The proof generalizes.** Although stated over $\mathbb{N}$, the
   argument never uses any specific arithmetic feature beyond the
   linear order. The same proof works verbatim for thresholds on
   $\mathbb{Z}$, $\mathbb{Q}$, $\mathbb{R}$, or any chain — making this
   entry a template for general one-dimensional PAC analyses.

4. **Tightness witness for Sauer-Shelah.** VC dim $= 1$ implies
   $\Pi_H(n) \leq n + 1$, and concretely $\Pi_{H_{\mathrm{thr}}}(n) =
   n + 1$ exactly (the $n + 1$ thresholds $t = 0, 1, \ldots, n$ produce
   $n + 1$ distinct labelings of any sorted $n$-point set). The
   Sauer-Shelah polynomial growth bound is *tight* for thresholds at
   every $n$.

5. **Concrete answer to OQ-01.** The parent gallery entry
   `pac-learning-bounds` formalizes the VC framework abstractly and
   asks whether VC dimension can be computed for specific classes. This
   entry answers *yes*, in 86 lines of Lean.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| pac-learning-bounds | Parent OQ. Formalizes VC dimension and PAC framework abstractly. This entry is a concrete instance of OQ-01. |
| pac-learning-bounds-oq-03 | Related open question on the same parent (other angles of VC dimension computation). |

## Current Formalization Status

**COMPLETED (verified)** — see `state.md`.

- `proofs/Proofs/PACLearningOQ01.lean`: 86 lines, **0 sorries**,
  **0 axioms**, status `verified`.
- 2 definitions: `Shatters`, `thresholdClassifiers`.
- 3 theorems: `threshold_shatters_singleton` (lower bound),
  `threshold_not_shatters_pair` (upper bound), `threshold_vcdim_bounds`
  (combined).
- Mathlib version: 4.26.0.
- Date added: 2026-04-27.

## References

- Vapnik, V. N. & Chervonenkis, A. Ya. (1971). *On the uniform
  convergence of relative frequencies of events to their probabilities.*
  Theory of Probability and Its Applications 16(2), 264–280.
- Blumer, A.; Ehrenfeucht, A.; Haussler, D.; Warmuth, M. K. (1989).
  *Learnability and the Vapnik-Chervonenkis dimension.* Journal of the
  ACM 36(4), 929–965.
- Shalev-Shwartz, S. & Ben-David, S. (2014). *Understanding Machine
  Learning: From Theory to Algorithms,* Chapter 6 (Cambridge UP).
