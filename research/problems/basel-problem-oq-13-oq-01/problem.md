# Problem: Dirichlet eta value η(4) = 7π⁴/720

**Slug**: basel-problem-oq-13-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\eta(4) \;=\; \sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n^4} \;=\; \frac{7\pi^4}{720}.
$$

### Plain Language

The parent entry (`basel-problem-oq-13`) proves the odd-fourth-power sum
$\lambda(4) = \sum_{k\ge 0} \tfrac{1}{(2k+1)^4} = \tfrac{\pi^4}{96}$. This leaf derives the
**Dirichlet eta** value at $4$, $\eta(4) = \tfrac{7\pi^4}{720}$, by splitting the alternating sum
into its odd and even parts: $\eta(4) = \lambda(4) - (\text{even-fourth-power sum})$, where the
even part is $\sum_{k\ge1} \tfrac{1}{(2k)^4} = \tfrac{1}{16}\zeta(4) = \tfrac{\pi^4}{1440}$.

### Why This Matters

$\eta(4)$ is the canonical alternating zeta value at $4$; the derivation cleanly demonstrates the
parity-split relation $\eta(s) = (1 - 2^{1-s})\zeta(s)$ at $s = 4$ and ties together the
odd-power $\lambda$, even-power, and full $\zeta$ sums. It also sets up the general
$\eta(2m) = (1 - 2^{1-2m})\zeta(2m)$ abstraction (sibling `basel-problem-oq-14-oq-01`).

### Why $7\pi^4/720$

$\eta(4) = (1 - 2^{-3})\zeta(4) = \tfrac{7}{8}\cdot\tfrac{\pi^4}{90} = \tfrac{7\pi^4}{720}$, and
equivalently $\lambda(4) - \tfrac{\pi^4}{1440} = \tfrac{\pi^4}{96} - \tfrac{\pi^4}{1440} = \tfrac{7\pi^4}{720}$.

## Known Results

### What's Already Proven

- Parent `basel-problem-oq-13`: $\lambda(4) = \sum_{k\ge0}(2k+1)^{-4} = \pi^4/96$ (verified).
- Mathlib: `Real.hasSum_zeta_four` ($\zeta(4) = \pi^4/90$) and the `riemannZeta`/`hasSum` API.

### What's Still Open

- The eta value $\eta(4) = 7\pi^4/720$ via the odd/even parity split (this entry).

### Our Goal

Prove $\sum_{n\ge1} (-1)^{n+1} n^{-4} = 7\pi^4/720$ by combining the parent's $\lambda(4)$ with the
even-index sum $\sum_{k\ge1}(2k)^{-4} = \tfrac1{16}\zeta(4) = \pi^4/1440$, regrouping the
alternating series into odd-minus-even.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| basel-problem-oq-13 | Direct parent; λ(4) = π⁴/96 | hasSum, odd-index zeta sum |
| basel-problem-oq-09-oq-01 | Sibling cluster; λ(4)/ζ(4) values | hasSum_zeta_four |
| basel-problem-oq-14-oq-01 | Sibling; general η(2m) abstraction | parity split |

## Initial Thoughts

### Potential Approaches

1. **Odd/even regrouping of the alternating sum**: $\eta(4) = \lambda(4) - \sum_{k\ge1}(2k)^{-4}$.
   The even-index sum is $\tfrac1{16}\zeta(4)$ by factoring $2^4$; use `Real.hasSum_zeta_four`.
   Then $\eta(4) = \pi^4/96 - \pi^4/1440$, finished by `ring`/`norm_num` on the rational coefficients.
   - Why it might work: both ingredients are already available as `hasSum` facts; the rest is algebra.
   - Risk: rearranging the alternating `hasSum` into odd/even sub-series (use
     `HasSum` even/odd splitting lemmas, e.g. `hasSum_even_add_odd` style).

### Key Difficulties

- Cleanly splitting the alternating series into its odd and even sub-sums as `HasSum` objects.

### What Would a Proof Need?

- Key lemma 1: even-index sum $\sum_{k\ge1}(2k)^{-4} = \tfrac1{16}\zeta(4)$ as a `HasSum`.
- Key lemma 2: alternating split $\eta(4) = \lambda(4) - \text{even}$ via a `HasSum` reindexing.
- Final: `norm_num`/`ring` to combine $\pi^4/96 - \pi^4/1440 = 7\pi^4/720$.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- Both numeric ingredients ($\lambda(4)$, $\zeta(4)$) are already verified in the gallery/Mathlib.
- The work is a `HasSum` odd/even regrouping plus rational arithmetic.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days

## References

### Mathlib
- `Mathlib.NumberTheory.ZetaValues` / `Real.hasSum_zeta_four` — $\zeta(4) = \pi^4/90$.
- `Mathlib.Topology.Algebra.InfiniteSum.*` — `HasSum` even/odd splitting and reindexing.

## Metadata

```yaml
tags:
  - analysis
  - zeta-function
  - eta-function
  - basel
related_proofs:
  - basel-problem-oq-13
  - basel-problem-oq-09-oq-01
  - basel-problem-oq-14-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
