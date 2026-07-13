# Problem: Partial sums of Lucas numbers

**Slug**: lucas-sum-oq-01
**Created**: 2026-06-25
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\sum_{k=1}^{n} L_k = L_{n+2} - 3
$$

where $L_1 = 1,\ L_2 = 3,\ L_{k+2} = L_{k+1} + L_k$ are the Lucas numbers.

### Plain Language

Adding up the first n Lucas numbers (1, 3, 4, 7, 11, …) gives the Lucas number two
places further along, minus 3. For example 1+3+4 = 8 = L₅ − 3 = 11 − 3.

### Why This Matters

This is the Lucas analogue of the well-known Fibonacci telescoping sum
∑F_k = F_{n+2} − 1, which already appears in the gallery. Mathlib provides
`Nat.fib` but no packaged Lucas-number partial-sum lemma, so this is a clean gallery
gap that exercises a second-order linear recurrence by induction.

## Known Results

### What's Already Proven

- ∑_{k=1}^n F_k = F_{n+2} − 1 — Fibonacci telescoping sum (gallery + Mathlib `Nat.fib` lemmas).
- Lucas/Fibonacci relations such as L_n = F_{n−1} + F_{n+1} — standard identities.

### What's Still Open

- A named Lucas partial-sum lemma in Mathlib.
- A self-contained Lucas definition (since Mathlib centers on `Nat.fib`).

### Our Goal

Prove ∑_{k=1}^{n} L_k = L_{n+2} − 3 in Lean 4, axiom-free, either with a
self-contained Lucas recurrence or via the identity L_n = F_{n−1} + F_{n+1} over `Nat.fib`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fibonacci-identities | Direct Fibonacci analogue ∑F_k = F_{n+2}−1 | induction, recurrence |
| lucas-cassini (combinations-formula) | Same Lucas-number objects | recurrence, induction |

## Initial Thoughts

### Potential Approaches

1. **Self-contained Lucas recurrence**: define `L : ℕ → ℕ` with L 0 = 2, L 1 = 1,
   L (n+2) = L (n+1) + L n; induct using the recurrence so the telescoping is exact.
   - Why it might work: the recurrence makes the inductive step L_{n+2} appear directly.
   - Risk: aligning the 1-indexed sum with a 0-indexed definition; constant offset (2 vs 3).

2. **Via Nat.fib using L_n = F_{n−1} + F_{n+1}**: reuse the Fibonacci sum lemma.
   - Why it might work: leans on existing Mathlib fib machinery.
   - Risk: index shifting and proving the L-to-F bridge first.

### Key Difficulties

- Index alignment between the 1-based sum and 0-based recurrence.
- Choosing initial conditions (L₀=2, L₁=1) consistently with the offset −3.

### What Would a Proof Need?

- Key lemma 1: the Lucas recurrence (own definition) or L_n = F_{n−1} + F_{n+1}.
- Key lemma 2: Finset.sum_range_succ for the inductive unfolding.
- Technical requirements: induction, omega/ring for the arithmetic offset.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- A standard telescoping induction over a second-order linear recurrence.
- The Fibonacci analogue is already formalized; structure carries over.
- Mathlib `Nat.fib` provides a fallback route if a self-contained Lucas def is preferred.

**Estimated Effort**:
- Exploration: under 1 hour
- If tractable: a few hours
- If hard: not expected

## References

### Papers
- Folklore Lucas-number identity; no paper required.

### Online Resources
- OEIS A000032 (Lucas numbers) and partial-sum relation L_{n+2} − 3.

### Mathlib
- Mathlib.Algebra.BigOperators.Basic — Finset.sum_range_succ.
- Mathlib.Data.Nat.Fib.Basic — `Nat.fib` (for the bridge route).

## Metadata

```yaml
tags:
  - number-theory
  - lucas-numbers
  - recurrence
  - telescoping
related_proofs:
  - fibonacci-identities
  - lucas-cassini
difficulty: low
source: gallery-gap
created: 2026-06-25
```
