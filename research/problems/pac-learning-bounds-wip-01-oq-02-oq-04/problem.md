# Problem: Covering-number bounds via pseudo-dimension / fat-shattering dimension

**Slug**: pac-learning-bounds-wip-01-oq-02-oq-04
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For a real-valued function class $\mathcal{F} \subseteq [0,1]^{\mathcal{X}}$ with
pseudo-dimension $\mathrm{Pdim}(\mathcal{F}) = d$ (resp. fat-shattering dimension
$\mathrm{fat}_\gamma(\mathcal{F})$), establish a polynomial covering-number bound of
Sauer–Shelah type:
$$
\mathcal{N}\!\left(\gamma,\ \mathcal{F},\ L^\infty(x_{1:m})\right)
\;\le\; \sum_{k=0}^{d}\binom{m}{k}\left(\tfrac{2}{\gamma}\right)^{k}
\;=\; O\!\left((m/\gamma)^{d}\right),
$$
i.e. lift the Boolean growth-function bound $|\Pi_{\mathcal H}(m)| \le \sum_{k\le d}\binom{m}{k}$
to real-valued classes by replacing VC dimension with pseudo-/fat-shattering dimension.

### Plain Language

The parent gallery proof formalizes the **Sauer–Shelah lemma** for Boolean concept
classes: a class of VC dimension $d$ can label at most $\sum_{k\le d}\binom{m}{k}$
subsets of $m$ points. This problem asks whether the same "transport" argument extends
to **real-valued** function classes, where VC dimension is replaced by the
**pseudo-dimension** or **fat-shattering dimension**, yielding polynomial bounds on
covering numbers (the real-valued analogue of the growth function).

### Why This Matters

Covering-number bounds via fat-shattering dimension are the backbone of uniform
convergence and generalization guarantees for regression and real-valued learning
(Alon–Ben-David–Cesa-Bianchi–Haussler). Formalizing the discretization-plus-Sauer–Shelah
transport would extend the gallery's learning-theory coverage from classification to
regression, and exercise combinatorial-analytic bridge lemmas rarely seen in Mathlib.

## Known Results

### What's Already Proven

- Sauer–Shelah / growth-function bound for Boolean classes — gallery proof
  `pac-learning-bounds-wip-01-oq-02`.
- Classical (paper) results: pseudo-dimension bounds (Pollard), fat-shattering
  covering-number bounds (Alon–Ben-David–Cesa-Bianchi–Haussler 1997).

### What's Still Open (for this formalization)

- A Lean definition of pseudo-dimension and fat-shattering dimension.
- The discretization lemma reducing a $\gamma$-cover to a Boolean shattering count.
- The polynomial covering-number bound itself.

### Our Goal

Prove the pseudo-dimension covering bound first (cleanest reduction to the Boolean
Sauer–Shelah lemma via thresholding), then, if tractable, the fat-shattering version.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| pac-learning-bounds-wip-01-oq-02 | Boolean Sauer–Shelah scaffold to transport | shifting/shattering, growth function |
| pac-learning-bounds-wip-01 | PAC sample-complexity framing | VC dimension, uniform convergence |

## Initial Thoughts

### Potential Approaches

1. **Approach A — pseudo-dimension via thresholding to Boolean case**:
   Reduce a real class to the Boolean class of subgraph indicators
   $\{(x,t)\mapsto \mathbf{1}[f(x)\ge t]\}$; its VC dimension is the pseudo-dimension;
   apply the existing Sauer–Shelah lemma.
   - Why it might work: directly reuses the formalized Boolean bound.
   - Risk: defining the subgraph class and relating its VC dim to $\mathrm{Pdim}$.

2. **Approach B — fat-shattering via $\gamma$-discretization**:
   Discretize outputs at scale $\gamma$, bound the number of distinct
   $\gamma$-quantized behaviors by a fat-shattering Sauer–Shelah count.
   - Why it might work: standard ABCH argument.
   - Risk: the discretization/counting step is analytically heavier to formalize.

### Key Difficulties

- No pseudo-/fat-shattering dimension primitives in Mathlib — must be defined.
- The $L^\infty$ covering-number formalism and its interaction with discretization.

### What Would a Proof Need?

- Key lemma 1: $\mathrm{Pdim}(\mathcal F) = \mathrm{VCdim}(\text{subgraph class})$.
- Key lemma 2: a $\gamma$-cover count is bounded by a Boolean shattering count.
- Technical requirements: covering-number definitions, thresholding maps.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The Boolean scaffold exists, but the real-valued dimension theory is new to formalize.
- Approach A (pseudo-dimension) is a clean reduction and is the recommended entry point.
- Fat-shattering discretization is heavier and may be a follow-up.

**Estimated Effort**:
- Exploration: 2–3 days scoping definitions
- If tractable: weeks (definitions + reduction + bound)
- If hard: fat-shattering route open-ended

## References

### Papers
- Alon, Ben-David, Cesa-Bianchi, Haussler, *Scale-sensitive dimensions...* (JACM 1997).
- Pollard, *Convergence of Stochastic Processes* (1984) — pseudo-dimension.
- Anthony & Bartlett, *Neural Network Learning* (1999), Ch. 11–12.

### Online Resources
- Lecture notes on fat-shattering and covering numbers (various ML theory courses).

### Mathlib
- The gallery Sauer–Shelah formalization — Boolean growth-function bound to transport.
- `Finset.card`, binomial-sum lemmas — for the counting bound.

## Metadata

```yaml
tags:
  - pac-learning
  - pseudo-dimension
  - fat-shattering
  - learning-theory
  - covering-numbers
related_proofs:
  - pac-learning-bounds-wip-01-oq-02
  - pac-learning-bounds-wip-01
difficulty: high
source: gallery-gap
created: 2026-07-04
```

**Significance**: 6/10
**Tractability**: 5/10
