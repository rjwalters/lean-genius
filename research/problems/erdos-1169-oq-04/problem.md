# Problem: Ordinal Partition Relation Formalization in Lean 4

**Slug**: erdos-1169-oq-04
**Created**: 2026-04-22T14:30:59+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

**OQ-04 of Erdős #1169**: Can the ordinal partition relation
$$\omega_1^2 \to (\omega_1^2, 3)^2$$
be fully formalized in Lean 4 using Mathlib's ordinal and coloring theory,
**replacing the current axiomatization**?

Specifically: eliminate the `axiom hajnal_ch_implies_partition` and related
axioms in `Proofs/Erdos1169Problem.lean` by deriving them from Mathlib's
ordinal arithmetic primitives or by building a verified framework for
ordinal partition calculus.

### Plain Language

The parent gallery entry `erdos-1169` uses three axioms to encode:
1. Hajnal's CH-conditional theorem (ω₁² → (ω₁², k)² under CH)
2. The non-disprovability result (ZFC does not refute the relation)
3. The independence statement (under PFA/MA)

The question is whether Lean 4 + Mathlib can verify at least one of these
without the axiom shortcut. The most tractable target is:

**CH implies ω₁² → (ω₁², 3)²**: prove that under the assumption CH
(2^ℵ₀ = ℵ₁), every 2-coloring of pairs from ω₁² contains either a
red ω₁²-copy or a blue triangle.

### Why This Matters

The axiomatization in `erdos-1169` is mathematically sound but vacuous as
formal proof. Replacing even one axiom with a proved theorem would:
- Demonstrate that ordinal partition calculus is within reach of Lean 4
- Create reusable infrastructure for Ramsey theory on uncountable ordinals
- Potentially connect to Mathlib's `Mathlib.SetTheory.Game.Ordinal` and
  `Mathlib.Combinatorics.Ramsey` modules

## Known Results

### What's Already Proven in the Gallery

- **erdos-1169** (axiomatized): The problem statement, Hajnal's result,
  and non-disprovability encoded as axioms. File:
  `Proofs/Erdos1169Problem.lean` (225 lines, 3 axioms)
- `ordinalPartitionRel` defined: ∀ 2-colorings, ∃ order-type-β monochromatic-0
  set OR k-clique (using StrictMono embeddings into Ordinal)
- `negPartitionRel` as the negation is defined

### Mathlib Resources

- `Mathlib.SetTheory.Ordinal.Arithmetic` — ordinal arithmetic (mul, add, pow)
- `Mathlib.SetTheory.Cardinal.Basic` — ℵ₀, ℵ₁, cardinal arithmetic
- `Mathlib.SetTheory.Cardinal.Ordinal` — ordinal/cardinal relationships
- `Mathlib.Combinatorics.Ramsey` — finite Ramsey theory
- `Mathlib.Order.TypeTags` — order-type embeddings

### What's Still Open

- Proving Hajnal's theorem in Lean 4 (requires CH and transfinite induction)
- Proving non-disprovability (requires model-theoretic argument)
- The main ZFC status (open mathematical problem)

### Our Goal

**Phase 1** (most tractable): Prove `ω → (ω, 3)²` (Ramsey theorem for ω)
without axioms, testing the infrastructure.

**Phase 2** (ambitious): Formalize Hajnal's proof sketch under CH for the
uncountable case.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-1169` | Parent problem, axioms to replace | Ordinal arithmetic, CH |
| `erdos-476-oq-05` | Combinatorial extremal theory | Finset, induction |
| `erdos-263` | Irrationality sequences, analytic methods | Series, real analysis |

## Initial Thoughts

### Potential Approaches

1. **Countable Ramsey First** (recommended starting point):
   - Prove `ω → (ω, 3)²` via infinite Ramsey theorem
   - Mathlib has `Mathlib.Combinatorics.Ramsey` for finite case
   - The infinite case (Ramsey for ω) may be in `Infinite` section
   - Why it might work: Tests infrastructure before hard uncountable case
   - Risk: Even infinite Ramsey for ω may need significant machinery

2. **Axiom Weakening**:
   - Replace Hajnal axiom with a weaker proved theorem
   - E.g., prove ω₁ → (ω₁, 3)² under CH (linear instead of square)
   - Risk: Even this requires careful ordinal induction

3. **Structural Infrastructure Only**:
   - Prove monotonicity: if α → (β, k)² and α' ≥ α, then α' → (β, k)²
   - These follow directly from `ordinalPartitionRel` definition
   - Risk: Not mathematically deep, but good for establishing framework

### Key Difficulties

- Ordinal induction at ω₁ requires CH axioms in ZFC
- Mathlib's Ramsey module is finite; extending to infinite ordinals is nontrivial
- The coloring in `ordinalPartitionRel` is on all pairs, not just a finset

### What Would a Proof Need?

- Key lemma 1: Infinite Ramsey theorem for ω (i.e., ω → (ω, 3)²)
- Key lemma 2: Monotonicity of partition relations under embedding
- Key lemma 3: CH implies specific cardinality bounds on ω₁ subsets
- Technical: `StrictMono` embeddings between ordinals in Mathlib

## Tractability Assessment

**Difficulty**: High for full Hajnal result; Medium for countable case; Low for structural lemmas

**Justification**:
- The full CH-conditional result requires significant set-theory expertise
- Countable Ramsey (ω → (ω,3)²) may already be in Mathlib or derivable
- Structural monotonicity lemmas follow from `ordinalPartitionRel` definition

**Estimated Effort**:
- Exploration: 1 day (inventory Mathlib ordinal/Ramsey API)
- If countable case tractable: 2-3 days
- Full CH-conditional: weeks (if at all possible without new Mathlib)

## References

### Papers
- Hajnal, A. (1964). "Some results and problems on set theory." Acta Math. Hungarica 14.
- Vàšíček, J. (1999). "Cardinal Arithmetic." [Va99 7.85]

### Online Resources
- https://erdosproblems.com/1169 — Problem statement and known results

### Mathlib
- `Mathlib.SetTheory.Ordinal.Arithmetic` — `Ordinal.mul`, transfinite induction
- `Mathlib.SetTheory.Cardinal.Basic` — `Cardinal.aleph`, `Cardinal.aleph0`
- `Mathlib.Combinatorics.Ramsey` — finite Ramsey theory
- `Mathlib.Order.RelClasses` — `StrictMono`, order embeddings

## Metadata

```yaml
tags:
  - set-theory
  - ramsey-theory
  - ordinals
  - combinatorics
  - erdos
  - formalization
related_proofs:
  - erdos-1169
difficulty: high
source: gallery-gap
created: 2026-04-22T14:30:59+02:00
```

**Significance**: 8/10
**Tractability**: 5/10
