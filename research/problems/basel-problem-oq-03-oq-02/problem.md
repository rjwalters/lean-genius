# Problem: Euler's reflection ζ(2,1) = ζ(3) — the first multiple-zeta-value relation

**Slug**: basel-problem-oq-03-oq-02
**Created**: 2026-07-02T02:47:20-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\zeta(2,1) \;=\; \sum_{m > n \ge 1} \frac{1}{m^2\, n} \;=\; \zeta(3) \;=\; \sum_{k \ge 1} \frac{1}{k^3}.
$$

Formalize Euler's reflection identity expressing the weight-3 double zeta value `ζ(2,1)` in terms of
the single odd zeta value `ζ(3)`. Here `ζ(s₁, s₂) = Σ_{m>n≥1} 1/(m^{s₁} n^{s₂})` is the (double)
multiple zeta value with the standard `m > n` summation convention.

### Plain Language

Multiple zeta values (MZVs) generalize `ζ(s)` to nested sums over strictly decreasing indices. The
simplest nontrivial relation among them, due to Euler, is `ζ(2,1) = ζ(3)`: the double sum
`Σ_{m>n} 1/(m²n)` collapses to the ordinary Apéry-constant series `Σ 1/k³`. This is the entry point
to the entire theory of MZV relations.

### Why This Matters

The parent chain descends from the Basel problem (`ζ(2) = π²/6`) into zeta-value identities. Euler's
`ζ(2,1) = ζ(3)` is the canonical first MZV relation and a natural, self-contained target: it
introduces the double-sum object and proves a clean closed relation using summation-by-parts /
partial-fraction (`1/(m²n)` telescoping) techniques that Mathlib's analysis library supports. It
extends the gallery's zeta-function material into the modern MZV setting.

## Known Results

### What's Already Proven

- Basel problem and `ζ(2) = π²/6` (parent chain) — infrastructure for zeta sums.
- Mathlib `Real.summable_one_div_nat_rpow` / `riemannZeta`, `tsum` manipulations, and Abel/partial
  summation lemmas.
- The classical proof: symmetrize `ζ(2,1)` and `ζ(1,2)`-type sums, or use the stuffle/shuffle
  relation `ζ(2)ζ(1)`-style manipulation; most elementary route is the partial-fraction identity
  `1/(m²n) = 1/(mn(m−n)) − ...` combined with telescoping.

### What's Still Open

- A Lean formalization of the double sum `ζ(2,1)` and the identity `ζ(2,1) = ζ(3)` (this problem).

### Our Goal

Define the double zeta value `ζ(2,1)` as an iterated `tsum` over `m > n ≥ 1`, establish its
summability, and prove it equals `ζ(3)`. Scope is the single identity; the general MZV theory is
out of scope.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| basel-problem | Ancestor; ζ(2) = π²/6 and zeta-sum infrastructure | Fourier / telescoping sums |
| basel-problem-oq-03 | Parent; zeta-value extensions | series manipulation |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Partial fractions + telescoping.
   - Why it might work: decompose `1/(m²n)` for `m > n` via partial fractions in `n` and reindex to
     telescope the inner sum, reducing the double sum to `Σ 1/k³`. Elementary and Mathlib-friendly.
   - Risk: careful handling of the `m > n` boundary and rearrangement of absolutely convergent
     double series (`Summable` / `tsum_comm`) is needed.

2. **Approach B**: Euler's symmetry relation `ζ(a,b) + ζ(b,a) = ζ(a)ζ(b) − ζ(a+b)`.
   - Why it might work: with `a = 2, b = 1` this and the sum-formula `ζ(2,1) = ζ(3)` pin down the
     value; may combine with the stuffle product.
   - Risk: `ζ(1)` diverges, so the symmetry route needs the regularized/limiting form — trickier to
     formalize than Approach A.

### Key Difficulties

- Rigorous handling of iterated infinite sums and rearrangements (`Summable`, `tsum_prod`,
  `tsum_comm`) over the region `m > n`.
- Avoiding the divergent `ζ(1)` in any symmetry-based manipulation.

### What Would a Proof Need?

- Key lemma 1: summability of `1/(m²n)` over `{(m,n) : m > n ≥ 1}` and a Fubini/`tsum_comm` step.
- Key lemma 2: the partial-fraction + telescoping reduction to `Σ 1/k³`.
- Technical requirements: `tsum`, `Summable`, partial fractions over `ℚ`/`ℝ`.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- Mathlib has strong `tsum`/`Summable` support and zeta infrastructure, but MZV-specific lemmas are
  essentially absent, so the double-sum bookkeeping is built from scratch.
- The mathematics is classical and the elementary telescoping proof is well-documented.
- Comparable single-zeta and telescoping-series formalizations exist in the gallery.

**Estimated Effort**:
- Exploration: days
- If tractable: 1–2 weeks
- If hard: unknown (if the double-sum rearrangement lemmas prove delicate)

## References

### Papers
- L. Euler — original derivation of `ζ(2,1) = ζ(3)`.
- M. E. Hoffman, "Multiple harmonic series" (1992) — modern MZV framework.

### Online Resources
- https://en.wikipedia.org/wiki/Multiple_zeta_function — `ζ(2,1) = ζ(3)` and MZV relations.

### Mathlib
- `Mathlib.Analysis.PSeries` / `Mathlib.NumberTheory.ZetaValues` — zeta-sum summability.
- `Mathlib.Topology.Algebra.InfiniteSum.*` — `tsum`, `tsum_comm`, `Summable`.

## Metadata

```yaml
tags:
  - number-theory
  - zeta-function
  - multiple-zeta-values
  - series
  - apery-constant
related_proofs:
  - basel-problem
  - basel-problem-oq-03
difficulty: high
source: proof-suggestion
created: 2026-07-02T02:47:20-07:00
```

**Significance**: 7/10
**Tractability**: 5/10
