# Problem: Glaisher Bijection as a Computable Function in Lean

**Slug**: partition-theorem-oq-04
**Created**: 2026-04-03T05:03:40-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{Define a Lean computable function } f : \mathcal{P}_{\text{odd}} \to \mathcal{P}_{\text{distinct}}
$$
$$
\text{such that } f \text{ realizes the Glaisher bijection and is provably weight-preserving and bijective.}
$$

### Plain Language

Euler's Partition Theorem states that the number of partitions of any natural number n into **odd parts** equals the number of partitions into **distinct parts**. The Glaisher bijection is the canonical constructive proof: it maps each odd-part partition to a distinct-part partition by grouping repeated odd factors using binary representation (p appearing k times → parts p·2^{a_i} where k = Σ 2^{a_i}).

The open question is whether this bijection can be formalized in Lean 4 as a **computable function** — using `def` rather than `noncomputable def` — and whether its bijectivity and partition-preserving properties can be machine-verified.

### Why This Matters

The existing `partition-theorem` gallery proof uses non-constructive counting arguments. A computable Glaisher bijection would:
1. Give an **explicit constructive proof** of Euler's theorem
2. Demonstrate certified computable bijections in combinatorics
3. Be a candidate for **Mathlib** contribution

## Known Results

### What's Already Proven

- Euler's Partition Theorem (odd = distinct count) — `partition-theorem` gallery proof
- Rogers-Ramanujan and Schur identities — `partition-theorem-oq-01`
- Basic partition types exist in Mathlib via `Nat.Partition`

### What's Still Open

- Explicit computable Lean 4 definition of the Glaisher map
- Proof that the map preserves partition sum (weight)
- Proof of bijectivity

### Our Goal

Define a computable `glaisherMap` in Lean 4, prove it preserves partition sums, and prove bijectivity, giving a constructive proof of Euler's theorem.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `partition-theorem` | Parent proof — Euler's odd=distinct theorem | Counting argument |
| `partition-theorem-oq-01` | Rogers-Ramanujan and Schur identities | Gap conditions, modular arithmetic |

## Initial Thoughts

### Potential Approaches

1. **Binary grouping**: Represent odd part p appearing k times via binary digits of k; replace with distinct parts p·2^{a_i}.
   - Why it might work: Standard construction, mathematically well-understood
   - Risk: Proving termination for recursive grouping in Lean's type system

2. **Multiset/Finsupp approach**: Use `Multiset ℕ` for parts, `Finsupp ℕ ℕ` for multiplicity maps
   - Why it might work: Mathlib has good infrastructure for these types
   - Risk: Type-level bookkeeping between partition representations

### Key Difficulties

- `Nat.Partition` type vs custom partition types
- Proving binary grouping terminates under Lean's well-foundedness checker
- Constructing the inverse map for bijectivity

### What Would a Proof Need?

- Key lemma 1: Glaisher map output has all distinct parts
- Key lemma 2: Sum is preserved under the grouping
- Key lemma 3: Inverse map (splitting distinct even parts) is well-defined
- Technical: `Finsupp` or `Multiset` for multiplicity representation

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The bijection is elementary; formalized in Isabelle/HOL before
- Mathlib has `Nat.Partition` and `Multiset` infrastructure
- Main challenge is Lean-specific types, not mathematics

**Estimated Effort**:
- Exploration: 1-2 days (finding right Mathlib types)
- If tractable: 3-7 days (definition + bijectivity)
- If hard: 2-3 weeks

## References

### Papers
- Glaisher, J.W.L. — original bijection construction (19th century)
- Andrews, G.E., "The Theory of Partitions" (1976)

### Mathlib
- `Nat.Partition` — partition type
- `Multiset ℕ` — multiset arithmetic
- `Finsupp ℕ ℕ` — finitely supported functions (multiplicity maps)

## Metadata

```yaml
tags:
  - combinatorics
  - partitions
  - bijection
  - computability
  - euler-theorem
related_proofs:
  - partition-theorem
  - partition-theorem-oq-01
difficulty: medium
source: gallery-gap
created: 2026-04-03T05:03:40-07:00
```

**Significance**: 6/10
**Tractability**: 7/10
