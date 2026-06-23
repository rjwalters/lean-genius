# Problem: Jordan-Hölder Uniqueness Theorem for Finite Groups in Lean

**Slug**: abel-ruffini-galois-extensions-oq-04
**Created**: 2026-04-24
**Status**: Active
**Source**: gallery-gap — from `abel-ruffini-galois-extensions` OQ4

## Problem Statement

### Formal Statement

Any two composition series of a finite group are equivalent: they have the same length and the same composition factors up to permutation and isomorphism.

In Lean, the target is:

```lean
-- Instantiate JordanHolderLattice for subgroups of a finite group
instance : JordanHolderLattice (Subgroup G) := ...

-- Then apply the existing abstract theorem
theorem jordan_holder_groups (G : Type*) [Group G] [Finite G]
    (s₁ s₂ : CompositionSeries (Subgroup G))
    (hb : s₁.head = s₂.head) (ht : s₁.last = s₂.last) :
    CompositionSeries.Equivalent s₁ s₂ :=
  CompositionSeries.jordan_holder s₁ s₂ hb ht
```

### Plain Language

Any two ways of "breaking down" a finite group into simple pieces give the same list of simple groups (up to reordering). For example, the solvability chain $\{e\} \trianglelefteq V_4 \trianglelefteq A_4 \trianglelefteq S_4$ is the *unique* composition series for $S_4$ up to equivalence, with composition factors $\mathbb{Z}/2, \mathbb{Z}/2, \mathbb{Z}/3, \mathbb{Z}/2$.

### Why This Matters

Jordan-Hölder is foundational:
- Makes simple groups the "atoms" of finite group theory
- Proves the Abel-Ruffini solvability witness is uniquely determined
- Connects to the Classification of Finite Simple Groups
- Template for Jordan-Hölder in modules and rings (already in Mathlib for modules)

## Known Results

### What's Already Proven

- **Mathlib**: `CompositionSeries.jordan_holder` is proved abstractly for any `JordanHolderLattice` in `Mathlib.Order.JordanHolder`
- **Mathlib**: Module version `JordanHolderLattice` instance exists in `Mathlib.RingTheory.SimpleModule`
- **Gallery**: The specific chain $\{e\} \trianglelefteq V_4 \trianglelefteq A_4 \trianglelefteq S_4$ is in `abel-ruffini-galois-extensions`
- **Mathlib**: Second isomorphism theorem for groups in `Mathlib.GroupTheory.QuotientGroup.Basic`

### What's Still Open

- No `JordanHolderLattice (Subgroup G)` instance in Mathlib for groups (only modules)
- Connecting the abstract `Iso` type to quotient group isomorphisms for the group case

### Our Goal

Instantiate `JordanHolderLattice` for `Subgroup G` and apply `CompositionSeries.jordan_holder` to get the group-specific theorem. Optionally: verify the S₄ solvability chain is unique.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `abel-ruffini-galois-extensions` | Parent proof: uses S₄ composition chain | Normal subgroups, solvable groups |
| `sylow-theorem` | Sylow subgroups appear in composition series | Coset counting |

## Initial Thoughts

### Potential Approaches

1. **JordanHolderLattice instance for Subgroup G**
   - Define `Iso (H K : Subgroup G) := (K.subgroupOf H ≅ ...)` using the second isomorphism theorem
   - Prove the `isMaximal_inf_right_of_isMaximal_sup` and `second_iso_of_eq` axioms
   - Apply `CompositionSeries.jordan_holder` as a one-liner
   - Why it might work: all ingredients are in Mathlib; module version is the template
   - Risk: `JordanHolderLattice.Iso` definition requires careful type-matching

2. **Direct adaptation from module instance**
   - Copy the `Mathlib.RingTheory.SimpleModule` instance strategy
   - Replace `Submodule R M` with `Subgroup G`
   - The second isomorphism theorem plays the role of the module isomorphism theorem
   - Most principled approach

### Key Difficulties

- `JordanHolderLattice.Iso` is abstract — need to define what "isomorphism" means for quotient group pairs
- `isMaximal` in `JordanHolderLattice` means coverage by a single step — maps to normal subgroup of prime index
- Type universe issues when working with `Subgroup G` as a lattice

### What Would a Proof Need?

- `Subgroup.secondIso`: for $H \leq K$, $K / (H \cap K) \cong HK / H$
- `Subgroup.isMaximal_iff_simpleQuotient`: maximal normal subgroup ↔ simple quotient
- The `JordanHolderLattice` instance axioms checked against Mathlib's subgroup API

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Abstract theorem already proved in Mathlib — pure instantiation work
- Module version provides exact template to follow
- All component lemmas (second isomorphism, maximal subgroups) are in Mathlib
- No new mathematical ideas needed

**Estimated Effort**:
- Exploration: 1-2 hours (read JordanHolder.lean and SimpleModule.lean)
- If tractable: 1-3 days (define instance, prove 3-4 axioms)
- Main risk: finding the right `Iso` type definition

## References

### Mathlib
- `Mathlib.Order.JordanHolder` — abstract theorem and `JordanHolderLattice` typeclass
- `Mathlib.RingTheory.SimpleModule.Basic` — module `JordanHolderLattice` instance (template)
- `Mathlib.GroupTheory.Subgroup.Basic` — subgroup lattice API
- `Mathlib.GroupTheory.QuotientGroup.Basic` — quotient group and second isomorphism

## Metadata

```yaml
tags:
  - algebra
  - group-theory
  - finite-groups
  - composition-series
  - mathlib-gap
related_proofs:
  - abel-ruffini-galois-extensions
  - sylow-theorem
difficulty: medium
source: gallery-gap
created: 2026-04-24
```

**Significance**: 8/10
**Tractability**: 7/10
