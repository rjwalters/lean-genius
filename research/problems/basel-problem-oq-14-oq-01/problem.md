# Problem: Uniform Dirichlet eta values η(2m) = (1 − 2^{1−2m}) ζ(2m)

**Slug**: basel-problem-oq-14-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For every $m \ge 1$,
$$
\eta(2m) \;=\; \sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n^{2m}} \;=\; \bigl(1 - 2^{1-2m}\bigr)\,\zeta(2m),
$$
recovering $\eta(2) = \tfrac{\pi^2}{12}$, $\eta(4) = \tfrac{7\pi^4}{720}$, $\eta(6) = \tfrac{31\pi^6}{30240}$, …
uniformly.

### Plain Language

The parent entry (`basel-problem-oq-14`) and its cluster derive specific Dirichlet eta values
(e.g. $\eta(4) = 7\pi^4/720$) one exponent at a time. This leaf **abstracts the parity split into a
single exponent-agnostic statement**: for *all* even arguments $2m$, the alternating zeta equals
$(1 - 2^{1-2m})$ times the Riemann zeta, derived once from `hasSum_zeta_nat`. The individual values
then fall out as one-line specializations.

### Why This Matters

A single uniform lemma $\eta(2m) = (1 - 2^{1-2m})\zeta(2m)$ replaces an open-ended family of
per-exponent derivations and is the natural general form of the even/odd splitting argument. It
demonstrates that the value $\zeta(2m)$ never enters the relation — the factor $(1 - 2^{1-2m})$ comes
purely from removing the even-index sub-series $\sum_k (2k)^{-2m} = 2^{-2m}\zeta(2m)$.

### Why the factor is $(1 − 2^{1−2m})$

Split $\sum_n n^{-2m} = \sum_{\text{odd}} + \sum_{\text{even}}$ and
$\eta(2m) = \sum_{\text{odd}} - \sum_{\text{even}}$. Since $\sum_{\text{even}} = 2^{-2m}\zeta(2m)$ and
$\sum_{\text{odd}} = (1 - 2^{-2m})\zeta(2m)$, we get
$\eta(2m) = (1 - 2^{-2m})\zeta(2m) - 2^{-2m}\zeta(2m) = (1 - 2\cdot 2^{-2m})\zeta(2m) = (1 - 2^{1-2m})\zeta(2m)$.

## Known Results

### What's Already Proven

- Parent `basel-problem-oq-14`: $\eta(4) = 7\pi^4/720$ (verified).
- Sibling `basel-problem-oq-13-oq-01`: $\eta(4)$ via the odd/even split (verified).
- Sibling `basel-problem-oq-09-oq-01`: parity split λ(s) = (1 − 2^{−s})·Z exponent-agnostic abstraction (verified).
- Mathlib: `riemannZeta`, `hasSum_zeta_nat` (general $\zeta(2k)$), and `HasSum` even/odd splitting.

### What's Still Open

- The single uniform statement $\eta(2m) = (1 - 2^{1-2m})\zeta(2m)$ for all $m$ (this entry).

### Our Goal

Prove the uniform relation parameterized by $m$ by an even/odd `HasSum` regrouping of the alternating
zeta, with the even-index sub-series factored as $2^{-2m}\zeta(2m)$ — keeping $\zeta(2m)$ abstract so
that the concrete values $\eta(2), \eta(4), \eta(6)$ are immediate corollaries via `hasSum_zeta_nat`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| basel-problem-oq-14 | Direct parent; η(4) = 7π⁴/720 | HasSum, parity split |
| basel-problem-oq-13-oq-01 | Sibling; η(4) via odd/even split | hasSum_zeta_four |
| basel-problem-oq-09-oq-01 | Sibling; exponent-agnostic λ(s) parity abstraction | HasSum even/odd |

## Initial Thoughts

### Potential Approaches

1. **Exponent-agnostic even/odd `HasSum` split**: model $\eta(2m)$ as $\sum_n (-1)^{n+1}n^{-2m}$,
   split into even and odd indices via `hasSum_even_add_odd`, factor $2^{-2m}$ out of the even part,
   and keep $\zeta(2m) = Z$ symbolic.
   - Why it might work: sibling `basel-problem-oq-09-oq-01` already did the same abstraction for the
     $\lambda$ relation; this is the eta analogue with the $(1 - 2^{1-2m})$ coefficient.
   - Risk: handling the general exponent $2m$ in the `(2k)^{-2m} = 2^{-2m} k^{-2m}` factorization
     (`mul_rpow`/`mul_pow` with even exponent) and the `HasSum` reindexing for arbitrary $m$.

### Key Difficulties

- Keeping the proof uniform in $m$ rather than specializing — the even-index factorization
  $(2k)^{2m} = 2^{2m}k^{2m}$ must hold symbolically.
- Aligning with `hasSum_zeta_nat` so the concrete π-power values specialize cleanly.

### What Would a Proof Need?

- Key lemma 1: even/odd `HasSum` split of $\sum_n (-1)^{n+1} n^{-2m}$.
- Key lemma 2: $\sum_{k\ge1}(2k)^{-2m} = 2^{-2m} Z$ where $Z = \zeta(2m)$.
- Key lemma 3: assemble $\eta(2m) = (1 - 2^{1-2m})Z$; specialize via `hasSum_zeta_nat`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The sibling λ-abstraction (`oq-09-oq-01`) provides a near-template; the new work is the eta sign
  pattern and keeping the general even exponent $2m$ symbolic.

**Estimated Effort**:
- Exploration: hours–day
- If tractable: 2–4 days

## References

### Mathlib
- `Mathlib.NumberTheory.ZetaValues` — `hasSum_zeta_nat`, general even-zeta values.
- `Mathlib.Topology.Algebra.InfiniteSum.*` — `HasSum` even/odd splitting and reindexing.

## Metadata

```yaml
tags:
  - analysis
  - zeta-function
  - eta-function
  - basel
related_proofs:
  - basel-problem-oq-14
  - basel-problem-oq-13-oq-01
  - basel-problem-oq-09-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
