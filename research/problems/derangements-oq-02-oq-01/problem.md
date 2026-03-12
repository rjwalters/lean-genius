# Problem: Partial Derangements for Arbitrary Finite Types

**Slug**: derangements-oq-02-oq-01
**Created**: 2026-03-06
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall \alpha : \text{Type}^* [\text{Fintype } \alpha],\; S(\alpha, k) = \binom{|\alpha|}{k} \cdot D(|\alpha| - k)
$$

where S(α, k) counts permutations σ : α ≃ α with exactly k fixed points, and D(m) counts derangements of a set of size m.

### Plain Language

The number of permutations of any finite set that fix exactly k elements equals (ways to choose k fixed elements) × (derangements of the rest). Prove this for arbitrary `Fintype α`, not just `Fin n`.

### Why This Matters

Generalizing from `Fin n` to arbitrary `Fintype α` is a fundamental pattern in Mathlib. It demonstrates that combinatorial identities hold for abstract types, not just concrete numbers, enabling cleaner composition with other abstract results.

## Known Results

### What's Already Proven

- S(n, k) = C(n,k) · D(n-k) for natural numbers — `derangements-oq-02` (gallery proof)
- Mathlib has `Equiv.Perm` and `Equiv.Derangements`
- `Fintype.card` provides cardinality for abstract types

### What's Still Open

- Type-generic version for arbitrary `Fintype α`
- Bijection between (k-subset, derangement of complement) at type level
- Integration with Mathlib's permutation group infrastructure

### Our Goal

Prove the partial derangement formula for `α : Type* [Fintype α] [DecidableEq α]`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| derangements-oq-02 | Base formula for Fin n | Counting, inclusion-exclusion |

## Initial Thoughts

### Potential Approaches

1. **Direct bijection**: Build explicit Equiv between {σ : Perm α | fixedPoints σ = k} and Σ (S : Finset α), (S.card = k) × Derangements (α \ S)
   - Why it might work: Clean type-theoretic construction
   - Risk: Subtypes and coercions can be tricky

2. **Transfer from Fin n**: Use `Fintype.truncEquivFin` to reduce to the known Fin n case
   - Why it might work: Avoids re-proving the combinatorics
   - Risk: Transfer machinery may add complexity

### Key Difficulties

- Defining `fixedPoints σ` as a `Finset α` with decidable membership
- Expressing the complement `α \ S` as a `Fintype`
- Connecting `Derangements` on a subtype to the count D(|α|-k)

### What Would a Proof Need?

- Key lemma 1: `fixedPoints σ = {a | σ a = a}` is a `Finset`
- Key lemma 2: Bijection between (choice of fixed set, derangement of rest)
- Technical requirements: `DecidableEq α`, `Fintype` instances for subtypes

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The concrete formula is already proven; this is a generalization
- Mathlib's Fintype/Equiv.Perm infrastructure is mature
- Similar generalizations exist in Mathlib (e.g., Finset.card lemmas)

## References

### Mathlib
- `GroupTheory.Perm.Basic` — permutation group
- `Combinatorics.Derangements.Basic` — if it exists
- `Data.Fintype.Basic` — Fintype infrastructure

## Metadata

```yaml
tags:
  - combinatorics
  - permutations
  - derangements
  - fintype
  - generalization
related_proofs:
  - derangements-oq-02
difficulty: medium
source: gallery-gap
created: 2026-03-06
```

**Significance**: 6/10
**Tractability**: 7/10
