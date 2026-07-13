# Problem: Mirsky's theorem (hard direction) for finite posets, connected to Set.chainHeight

**Slug**: dilworth-theorem-oq-01-oq-03
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

**Mirsky's theorem (finite poset).** In a finite partially ordered set $P$, the maximum length of a chain equals the minimum number of antichains needed to cover $P$:

$$
\max_{\text{chain } C}\, |C| \;=\; \min\{\, k : P = A_1 \cup \dots \cup A_k,\ A_i \text{ antichains}\,\}.
$$

The nontrivial ("hard") direction is that the elements can be partitioned into $h$ antichains where $h$ is the longest chain length, via the height function $x \mapsto (\text{length of longest chain with top } x)$.

### Plain Language

Mirsky's theorem is the order-dual of Dilworth's theorem. Its hard direction says: label each element by the length of the longest chain ending at it; elements sharing a label form an antichain, so the poset splits into exactly (longest chain length) antichains. This problem asks to formalize that construction for finite posets and connect the "longest chain length" to Mathlib's `Set.chainHeight`.

### Why This Matters

Dilworth's theorem is in the gallery (parent, verified); Mirsky is its natural dual and a standard companion result. Formalizing the constructive hard direction and tying it to `Set.chainHeight` fills a recognized gap and reuses order-theoretic machinery.

## Known Results

### What's Already Proven

- Dilworth's theorem — parent proof `dilworth-theorem-oq-01` (verified).
- Mathlib `Set.chainHeight` / `Set.subchain` infrastructure for chain lengths.
- The easy direction of Mirsky (a chain meets each antichain at most once, so #antichains ≥ chain length).

### What's Still Open

- The constructive hard direction of Mirsky for finite posets in this repo.
- The precise bridge lemma expressing "longest chain length" as `Set.chainHeight` for a finite poset.

### Our Goal

Prove the hard direction of Mirsky's theorem for a finite poset: construct the antichain partition via the height function and show it uses exactly `h` antichains, where `h` is the longest chain length; and connect `h` to `Set.chainHeight (Set.univ : Set P)`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| dilworth-theorem-oq-01 | Parent: Dilworth's theorem (dual of Mirsky) | chain/antichain duality |
| dilworth-theorem-oq-01-oq-01 | Related Dilworth follow-ups and infrastructure | poset combinatorics |

## Initial Thoughts

### Potential Approaches

1. **Height-function partition**: Define $h(x)$ = length of the longest chain with maximum element $x$; show fibers $h^{-1}(k)$ are antichains and that $h$ ranges over $\{1,\dots,H\}$ with $H$ the longest chain length.
   - Why it might work: the classical proof is short and constructive; comparability forces distinct height values.
   - Risk: relating the in-file $h$ to `Set.chainHeight` (off-by-one and `ℕ∞` vs `ℕ` conventions).

2. **Dualize the parent Dilworth proof**: apply the parent to the order dual $P^{op}$.
   - Why it might work: Mirsky is literally Dilworth-dual for the antichain-cover form in some formulations — but note Dilworth (chains covering, antichain max) and Mirsky (antichains covering, chain max) are *not* the same statement, so care is needed; the direct height-function proof is safer.
   - Risk: the two theorems are duals only under the correct correspondence; may not import cleanly.

### Key Difficulties

- `Set.chainHeight` lives in `ℕ∞`; the finite longest-chain length must be extracted and matched.
- Showing each height fiber is an antichain (comparable elements would have different heights).

### What Would a Proof Need?

- Key lemma 1: for comparable $x < y$, $h(x) < h(y)$ (hence fibers are antichains).
- Key lemma 2: $\max_x h(x)$ equals the longest chain length / `Set.chainHeight`.
- Technical requirements: finiteness (`Fintype P`), well-founded recursion for $h$, `Set.chainHeight` lemmas.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is a standard short proof; difficulty is Lean plumbing around `Set.chainHeight` and `ℕ∞`.
- Dilworth parent shows the surrounding infrastructure is already usable in-repo.
- Finite posets keep everything decidable and well-founded.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: 3–5 days

## References

### Papers
- Mirsky, L. (1971), "A dual of Dilworth's decomposition theorem", *Amer. Math. Monthly*.

### Online Resources
- Wikipedia: "Mirsky's theorem", "Dilworth's theorem".

### Mathlib
- `Mathlib.Order.Chain`, `Set.chainHeight`, `Set.subchain` — chain-length infrastructure.
- `Fintype`, well-founded recursion — for the finite height function.

## Metadata

```yaml
tags:
  - order-theory
  - dilworth
  - mirsky
  - chain-height
related_proofs:
  - dilworth-theorem-oq-01
  - dilworth-theorem-oq-01-oq-01
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 6/10
