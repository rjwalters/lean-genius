# Problem: Explicit Modulus of Convergence for the Norm-Preserving Tietze Series

**Slug**: urysohns-lemma-oq-01-oq-01-oq-02-oq-02
**Created**: 2026-06-24
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\Big\| G - \sum_{i < n} g_i \Big\|_\infty \;\le\; \left(\tfrac{2}{3}\right)^{n} M ,
\qquad M = \|f\|_\infty ,
$$

where $G = \sum_{i} g_i \in X \to^{b} \mathbb{R}$ is the explicit Urysohn correction series
realizing the norm-preserving Tietze extension of $f \in C(s,\mathbb{R})$ from a closed
$s \subseteq X$ on a normal space $X$.

### Plain Language

The parent gallery proof (`urysohns-lemma-oq-01-oq-01-oq-02`) builds the Tietze extension $G$
as an *infinite sum* of geometrically shrinking continuous corrections $g_i$, and shows the sum
both converges and preserves the sup-norm, $\|G\| = \|f\|$. What it does **not** do is record
*how fast* the partial sums approach $G$. This problem asks for the explicit, quantitative
convergence rate: after summing the first $n$ corrections, the remaining error is at most
$(2/3)^n M$. In other words, we want a concrete *modulus of uniform convergence* for the series,
turning "the series converges" into "the series converges at this verified geometric rate."

### Why This Matters

A modulus of convergence is the computational content of the extension theorem: it tells you
exactly how many Urysohn steps suffice to approximate the extension to a prescribed tolerance,
making the construction effective rather than merely existential. Because each correction is
bounded by $\tfrac13(2/3)^i M$, the tail $\sum_{i \ge n} \|g_i\|$ is a geometric remainder, so
the bound is sharp up to the constant and follows directly from the engine lemmas already in
the parent. Establishing it upgrades the entry from "an extension exists" to "here is its
explicit rate of approximation," which is the pedagogically illuminating payoff of building
Tietze by hand instead of invoking Mathlib's closed-embedding machinery.

## Known Results

### What's Already Proven

- `urysohns-lemma-oq-01-oq-01-oq-02` (parent) — the norm-preserving Tietze extension assembled
  as an explicit `tsum` of corrections $g_i \in X \to^{b}\mathbb{R}$ with $\|G\| = \|f\|$.
- `urysohn_approx_step` / `urysohn_approx_iterate` (grandparent file
  `Proofs/UrysohnsLemmaOQ01OQ01.lean`) — the one-step correction bounded by $M/3$ that reduces
  the residual to $(2/3)M$, and its $n$-fold iterate giving residual $(2/3)^n M$ on $s$.
- Mathlib `BoundedContinuousFunction` is a complete normed space; `tsum`, `Summable`,
  `summable_of_summable_norm`, and the geometric-series remainder estimates
  (`tsum_geometric_of_lt_one`, summable-tail bounds for a series majorized in norm) are
  available.

### What's Still Open

- A clean statement and proof that the $n$-th partial sum $\sum_{i<n} g_i$ differs from the
  limit $G$ by at most $(2/3)^n M$ in sup-norm.
- Packaging this as a reusable rate/modulus lemma keyed to the parent's correction sequence.

### Our Goal

Prove a Lean lemma `tietze_series_tail_le` (or similar) stating
$\big\| G - \sum_{i<n} g_i \big\|_\infty \le (2/3)^n M$, derived purely from the per-term bound
$\|g_i\| \le \tfrac13 (2/3)^i M$ and the geometric tail estimate, with no appeal to
`ContinuousMap.exists_restrict_eq`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| urysohns-lemma-oq-01-oq-01-oq-02 | Direct parent; supplies the correction sequence $g_i$ and the norm-preserving sum $G$. | Explicit `tsum` in $X\to^b\mathbb{R}$, geometric sup-norm bounds, completeness |
| urysohns-lemma-oq-01-oq-01 | Engine: the one-step Urysohn correction and its $(2/3)^n$ iterate. | One-step approximation, geometric error decay |
| urysohns-lemma-oq-01 | Grandparent recording the "Tietze from Urysohn" open question. | Urysohn separation by continuous functions |

## Initial Thoughts

### Potential Approaches

1. **Approach A — geometric tail of the per-term bound**: Use $\|g_i\| \le \tfrac13(2/3)^i M$
   together with the summable-tail estimate to bound
   $\|G - \sum_{i<n}g_i\| = \|\sum_{i \ge n} g_i\| \le \sum_{i\ge n}\tfrac13(2/3)^i M = (2/3)^n M$.
   - Why it might work: the constant $\tfrac13 \cdot \tfrac{1}{1-2/3} = 1$ makes the tail close
     in one geometric-series computation.
   - Risk: matching Mathlib's exact tail-bound API (norm of a tsum tail vs. partial-sum distance).

2. **Approach B — re-derive from `urysohn_approx_iterate` residuals**: Show the partial sum
   equals the $n$-step iterate up to bookkeeping, then quote the iterate's $(2/3)^n M$ residual.
   - Why it might work: the residual bound is already proven for the iterate.
   - Risk: aligning the partial-sum indexing with the iterate's recursion.

### Key Difficulties

- Selecting the right Mathlib lemma relating a partial sum to the `tsum` tail in a Banach space.
- Keeping the $\tfrac13$ vs. $\tfrac{2}{3}$ constants exact so the final bound is clean $(2/3)^n M$.

### What Would a Proof Need?

- Key lemma 1: per-correction sup-norm bound $\|g_i\| \le \tfrac13(2/3)^i M$ (from the parent).
- Key lemma 2: tail of a summable series bounded by the tail of its norm-majorant.
- Technical requirements: geometric series sum `tsum_geometric_of_lt_one` with ratio $2/3$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The hard analytic content (summability, completeness, norm preservation) is already done in
  the parent; this is a quantitative tail estimate over an existing series.
- Closely parallels standard Mathlib geometric-remainder arguments.
- All needed APIs (`BoundedContinuousFunction`, geometric tsum) are in Mathlib.

**Estimated Effort**:
- Exploration: a few hours to locate the tail-bound lemma.
- Formalization: about one day for a clean reusable statement.
