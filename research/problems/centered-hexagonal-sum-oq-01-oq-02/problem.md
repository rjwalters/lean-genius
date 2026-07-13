# Problem: Combinatorial bijection between hexagonal and cubic shells

**Slug**: centered-hexagonal-sum-oq-01-oq-02
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\sum_{k=1}^{n} H_k = n^3, \qquad H_k = 3k(k-1) + 1,
$$

with the goal of realizing this identity via an **explicit bijection**

$$
\Phi : \bigsqcup_{k=1}^{n} (\text{$k$-th centered hexagonal shell}) \;\xrightarrow{\ \sim\ }\; \{0,1,\dots,n-1\}^3,
$$

matching each hexagonal shell $H_k$ to the $k$-th cubic shell $C_k = \{0,\dots,k-1\}^3 \setminus \{0,\dots,k-2\}^3$, so that $|C_k| = k^3 - (k-1)^3 = 3k(k-1)+1 = H_k$.

### Plain Language

The parent proof (`centered-hexagonal-sum-oq-01`) establishes algebraically that the sum of the first $n$ centered hexagonal numbers equals $n^3$, via telescoping/induction on closed forms. This open question asks whether the "cube-shell" picture behind the identity can be promoted to a genuinely **combinatorial** proof in Lean: exhibit a bijection between the $n$ hexagonal shells and the $n$ cubic shells $C_k = k^3 - (k-1)^3$, turning the identity into a counting statement rather than an algebraic one.

### Why This Matters

- Turns a computational identity into a structural one — the pedagogically preferred "proof from the book" for figurate-number identities.
- Establishes a reusable gallery pattern for shell-decomposition bijections ($\sum \text{shell}_k = \text{total}$), transferable to other figurate/polytopic identities (square pyramidal, octahedral).
- Bijective proofs are more robust under generalization than closed-form telescoping.

## Known Results

### What's Already Proven

- `centered-hexagonal-sum-oq-01` — algebraic identity $\sum_{k=1}^n H_k = n^3$ (parent, verified, 0-axiom).
- $k^3 - (k-1)^3 = 3k(k-1) + 1 = H_k$ — per-shell cardinality match is elementary (`ring`/`omega`).
- Mathlib `Finset.card_product`, `Finset.card_sdiff`, `Finset.card_biUnion` support the counting side.

### What's Still Open

- Construct the explicit map $\Phi$ (or, weakly, prove the two shell families are equinumerous shell-by-shell and assemble a global bijection).
- Decide the right Lean encoding of a "hexagonal shell" as a `Finset` whose card is $H_k$ so the bijection is checkable.

### Our Goal

Prove in Lean 4 + Mathlib that each $k$-th hexagonal shell is equinumerous with the cubic shell $C_k = \{0,\dots,k-1\}^3 \setminus \{0,\dots,k-2\}^3$, and derive $\sum_{k=1}^n H_k = n^3$ as a corollary via `Finset.card_biUnion` over the disjoint cubic shells. A full explicit coordinate bijection is a stretch goal; the shell-by-shell cardinality decomposition assembling into `card ({0,...,n-1}^3) = n^3` is the primary deliverable.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| centered-hexagonal-sum-oq-01 | Parent; provides the algebraic identity to re-prove bijectively | telescoping, induction, `ring` |
| combinations-formula-oq-10-oq-01 | Prior counting identity proved by re-indexing Finset sums | `Finset.sum_range_succ`, absorption |

## Initial Thoughts

### Potential Approaches

1. **Cubic-shell decomposition (recommended)**: Define $C_k = \{0,\dots,k-1\}^3 \setminus \{0,\dots,k-2\}^3$ as a `Finset (ℕ×ℕ×ℕ)`. Show the $C_k$ are pairwise disjoint with union $\{0,\dots,n-1\}^3$. Then `card` gives $n^3$, and `card C_k = H_k` by `ring`/`omega` on $k^3-(k-1)^3$.
   - Why it might work: the hard geometric bijection is avoided; shells are literal set differences of cubes, and disjoint-union card lemmas exist in Mathlib.
   - Risk: encoding the hexagonal side as a Finset of card exactly $H_k$ (to make the bijection literal, not just equinumerous) is fiddly.

2. **Explicit coordinate bijection**: give an actual `Equiv` between an enumerated hexagonal shell and $C_k$.
   - Why it might work: strongest form of the result.
   - Risk: high; needs a canonical linear ordering of both shells and an index formula — likely more effort than its marginal value.

### Key Difficulties

- Choosing a Finset model of the hexagonal shell whose cardinality is provably $H_k$.
- Proving disjointness and union-equals-full-cube cleanly with `Finset` set operations.

### What Would a Proof Need?

- Key lemma 1: `card (range k ×ˢ range k ×ˢ range k) = k^3` via `Finset.card_product`.
- Key lemma 2: `card (cube k \ cube (k-1)) = 3*k*(k-1)+1` — set-difference card of nested cubes, then `ring`.
- Key lemma 3: disjoint `biUnion` of the shells reconstructs the full cube — `Finset.card_biUnion` with pairwise disjointness.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The counting side is standard `Finset` cardinality manipulation well-supported in Mathlib.
- The per-shell cardinality equation is a one-line `ring`/`omega`.
- Only the "literal bijection on a hexagonal model" stretch goal is genuinely tricky; the decomposition form is tractable.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days
- If hard (full explicit `Equiv`): unknown

## References

### Papers
- Conway & Guy, *The Book of Numbers* (1996) — figurate numbers and shell decompositions.

### Online Resources
- OEIS A003215 (centered hexagonal numbers), A000578 (cubes).

### Mathlib
- `Mathlib.Data.Finset.Card` — `card_product`, `card_sdiff`, `card_biUnion`.
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum_range_succ`.

## Metadata

```yaml
tags:
  - combinatorics
  - figurate-numbers
  - bijective-proof
  - finset-cardinality
related_proofs:
  - centered-hexagonal-sum-oq-01
  - combinations-formula-oq-10-oq-01
difficulty: low
source: proof-suggestion
created: 2026-07-02
```
