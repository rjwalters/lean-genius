# Problem: Bijective witness for the weak-composition convolution

**Slug**: stars-and-bars-weak-compositions-oq-04-oq-02
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\Big\{\, f : \mathrm{Fin}\,(k_1+k_2) \to \mathbb{N} \ \Big|\ \textstyle\sum f = n \,\Big\}
\ \simeq\
\sum_{(a,b)\,\in\,\mathrm{antidiagonal}\,n}
\Big(\{ g : \mathrm{Fin}\,k_1 \to \mathbb{N} \mid \textstyle\sum g = a\} \times \{ h : \mathrm{Fin}\,k_2 \to \mathbb{N} \mid \textstyle\sum h = b\}\Big)
$$

### Plain Language

The parent entry proves the *cardinality* convolution identity for weak compositions:
the number of ways to write `n` as an ordered sum of `k₁+k₂` nonnegative integers equals
the sum over `a+b=n` of (ways for `k₁` parts summing to `a`) × (ways for `k₂` parts summing to `b`).
That is a numerical (Vandermonde-style) identity. The goal here is to promote it from an
equality of numbers to an explicit **bijection** (a Lean `Equiv`): split a tuple of length
`k₁+k₂` at index `k₁` into its first `k₁` coordinates and its last `k₂` coordinates, and
show this splitting is the constructive witness realizing the convolution.

### Why This Matters

A cardinality identity tells you the counts match; a bijection tells you *why*. Exposing the
`Equiv` makes the result composable — downstream proofs can transport structure across it,
and it is the honest combinatorial content of the convolution. It also demonstrates the
`Finset.antidiagonal` + `Fintype.card_sigma` idiom for turning counting arguments structural.

## Known Results

### What's Already Proven

- Parent `stars-and-bars-weak-compositions-oq-04`: the cardinality convolution identity.
- Mathlib `Finset.Nat.antidiagonal` and `Finset.Nat.card_antidiagonal`.
- Mathlib `Fintype.card_sigma`, `Fintype.card_prod`, `Fintype.card_congr`.

### What's Still Open

- The explicit `Equiv` (splitting map) and its inverse (concatenation map).
- The round-trip proofs (`left_inv` / `right_inv`) and the sum-preservation lemmas.

### Our Goal

Construct the `Equiv` above using `Fin.append` / `Fin.addCases` (or `finSumFinEquiv`) to
split and rejoin tuples, prove `∑` decomposes as `a + b` along the split, and derive the
parent's cardinality identity as a corollary of `Fintype.card_congr` applied to this `Equiv`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| stars-and-bars-weak-compositions-oq-04 | Direct parent; supplies the target cardinality identity | Finset counting, antidiagonal |
| stars-and-bars-weak-compositions | Base stars-and-bars result | binomial coefficients |

## Initial Thoughts

### Potential Approaches

1. **Split-at-`k₁` via `Fin.addCases`**: map `f` to `(f ∘ castAdd, f ∘ natAdd)`; the sigma
   index is `(∑ first, ∑ last)`, which lies in `antidiagonal n`.
   - Why it might work: `Fin.sum_univ_add` already splits the sum cleanly.
   - Risk: dependent-type bookkeeping in the sigma fibre (the index depends on the tuple).

2. **`finSumFinEquiv` transport**: reindex `Fin (k₁+k₂) ≃ Fin k₁ ⊕ Fin k₂` first, then
   split the `⊕`-indexed function.
   - Why it might work: keeps the sum-splitting lemma off the shelf.
   - Risk: extra coercion layer.

### Key Difficulties

- The sigma's fibre index is *determined by* the element, so the `Equiv` lands in a
  dependent sum over `antidiagonal n` — care needed to package membership proofs.
- Proving the round trips requires `Fin.append_left`/`Fin.append_right` simp lemmas.

### What Would a Proof Need?

- Key lemma 1: the total sum splits as first-block sum plus last-block sum.
- Key lemma 2: the split and concatenation maps are mutually inverse.
- Technical requirements: `Fin.addCases`, `Fin.sum_univ_add`, `Finset.Nat.antidiagonal`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The numerical result already exists; this is a structural refinement, not new mathematics.
- Mathlib has strong `Fin.append`/`addCases` support and the antidiagonal API.
- Similar sigma-cardinality bijections appear in Mathlib's combinatorics files.

**Estimated Effort**:
- Exploration: hours
- If tractable: days

## References

### Mathlib
- `Mathlib.Logic.Equiv.Fin` — `finSumFinEquiv`, `Fin.addCases`.
- `Mathlib.Algebra.BigOperators.Fin` — `Fin.sum_univ_add`.
- `Mathlib.Combinatorics.Enumerative.Composition` — related tuple/composition API.

## Metadata

```yaml
tags:
  - combinatorics
  - enumerative-combinatorics
  - stars-and-bars
  - weak-compositions
related_proofs:
  - stars-and-bars-weak-compositions-oq-04
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 6/10
