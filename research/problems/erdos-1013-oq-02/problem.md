# Problem: Unconditional Ratio Convergence of the Triangle-Free Chromatic Threshold

**Slug**: erdos-1013-oq-02
**Created**: 2026-07-03T23:49:35-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $h_3(k)$ be the least number of vertices in a triangle-free graph of chromatic
number $k$. The known window (Erdős, and refinements) is
$$
\left(\tfrac{1}{2} - o(1)\right) k^2 \log k \;\le\; h_3(k) \;\le\; \left(1 + o(1)\right) k^2 \log k .
$$
Open question (Erdős #1013, second open question):
$$
\frac{h_3(k+1)}{h_3(k)} \xrightarrow[k \to \infty]{} 1 \quad ?
$$
We seek an **unconditional** proof — i.e. without first assuming that the exact
asymptotic constant $c$ in $h_3(k) \sim c\,k^2 \log k$ exists.

### Plain Language

$h_3(k)$ measures how many vertices you need to force chromatic number $k$ while
staying triangle-free. Consecutive values grow by roughly the same multiplicative
factor as $k$ increases; the conjecture asks whether that factor tends to exactly $1$
(i.e. $h_3$ grows "smoothly", with no jumps in relative size).

### Why This Matters

Ratio convergence is the natural "regularity" statement one can hope to prove before
pinning down the exact constant $c \in [1/2, 1]$. It connects the extremal
graph-coloring problem to smoothness of the growth function and would be the first
unconditional structural result about $h_3$ beyond the two-sided window bounds.

## Known Results

### What's Already Proven

- Two-sided window $(1/2 - o(1))k^2\log k \le h_3(k) \le (1 + o(1))k^2\log k$ — Erdős; classical Ramsey/probabilistic bounds (gallery entry `erdos-1013`).
- **Conditional** ratio convergence — gallery sibling `erdos-1013-oq-01` proves: if the asymptotic constant $c > 0$ exists for *any* $c$, then $h_3(k+1)/h_3(k) \to 1$ follows automatically, and $c$ is then unique. Analytic core: machine-checked $\dfrac{(k+1)^2 \log(k+1)}{k^2 \log k} \to 1$.

### What's Still Open

- The exact constant $c$ in $h_3(k) \sim c\,k^2\log k$ (only known: $c \in [1/2, 1]$) — this is `erdos-1013-oq-01`'s question [0] and remains open.
- **Unconditional** ratio convergence: proving $h_3(k+1)/h_3(k) \to 1$ *without* assuming $c$ exists. This is the distinct gap left open by `oq-01`.

### Our Goal

Prove the strongest *unconditional* statement reachable from the window bounds:
the ratio $h_3(k+1)/h_3(k)$ is asymptotically trapped in a bounded interval. From
the window, for large $k$,
$$
\tfrac{1}{2}(1 - o(1)) \cdot \frac{(k+1)^2\log(k+1)}{k^2\log k}
\;\le\; \frac{h_3(k+1)}{h_3(k)} \;\le\;
2(1 + o(1)) \cdot \frac{(k+1)^2\log(k+1)}{k^2\log k},
$$
and since the middle factor $\to 1$ (already machine-checked in `oq-01`), we get
$$
\tfrac{1}{2} \le \liminf \frac{h_3(k+1)}{h_3(k)} \le \limsup \frac{h_3(k+1)}{h_3(k)} \le 2 .
$$
Target leaf: formalize this bounded-ratio result and cleanly isolate the reduction
"full convergence $\iff$ existence of $c$", making explicit exactly what remains open.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1013 | Parent entry: defines $h_3(k)$ and the window bounds | Ramsey/probabilistic bounds |
| erdos-1013-oq-01 | Proves conditional ratio convergence + the analytic limit $\frac{(k+1)^2\log(k+1)}{k^2\log k}\to1$; supplies the reusable core | asymptotic analysis, `Filter.Tendsto` |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Window squeeze (tractable leaf)**: Combine the lower and upper
   window bounds for $h_3(k)$ and $h_3(k+1)$ with the already-proven analytic limit
   to bound $\liminf/\limsup$ of the ratio in $[1/2, 2]$.
   - Why it might work: purely arithmetic once the window bounds are stated as hypotheses; the analytic core is reusable from `oq-01`.
   - Risk: gives only $[1/2,2]$, not convergence to $1$ — but it is unconditional and machine-checkable.

2. **Approach B — Direct sub-multiplicativity**: Seek a structural inequality
   $h_3(k+\ell) \le f(k,\ell)\,h_3(k)$ from graph products (categorical/tensor
   products preserving triangle-freeness) to control consecutive ratios directly.
   - Why it might work: would attack convergence itself, not just boundedness.
   - Risk: constructing triangle-free products with controlled chromatic number is the genuinely hard, open part.

### Key Difficulties

- Full convergence to $1$ is equivalent to (and no easier than) existence of the constant $c$ — the genuinely open core.
- The window constants $1/2$ and $1$ are not tight enough to force ratio $\to 1$ by squeezing alone.

### What Would a Proof Need?

- Key lemma 1: window bounds for $h_3$ as formal hypotheses (or as `axiom`/`variable` inputs citing Erdős).
- Key lemma 2: the analytic limit $\frac{(k+1)^2\log(k+1)}{k^2\log k}\to 1$ (import/adapt from `oq-01`).
- Technical requirements: `Filter.Tendsto`, `liminf`/`limsup` API, real-analysis lemmas in Mathlib.

## Tractability Assessment

**Difficulty**: Medium (for the bounded-ratio leaf) | Moonshot (for full convergence)

**Justification**:
- The bounded-ratio leaf reduces to arithmetic over already-established asymptotics.
- `oq-01` demonstrates the analytic infrastructure is available and machine-checkable.
- Full convergence is equivalent to an open problem (existence of $c$) and should not be attempted directly.

**Estimated Effort**:
- Exploration: hours
- If tractable (bounded-ratio leaf): days
- If hard (full convergence): unknown / open

## References

### Papers
- P. Erdős, work on chromatic number of triangle-free graphs — origin of $h_3(k)$ and the window bounds.

### Online Resources
- Erdős Problems #1013 — https://www.erdosproblems.com/1013

### Mathlib
- `Mathlib.Order.LiminfLimsup` — `liminf`/`limsup` of sequences.
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — logarithm asymptotics.
- `Mathlib.Topology.Algebra.Order` / `Filter.Tendsto` — limit manipulation.

## Metadata

```yaml
tags:
  - combinatorics
  - graph-theory
  - chromatic-number
  - triangle-free
  - ramsey-theory
  - asymptotics
related_proofs:
  - erdos-1013
  - erdos-1013-oq-01
difficulty: medium
source: gallery-gap
created: 2026-07-03T23:49:35-07:00
```

**Significance**: 6/10
**Tractability**: 5/10
