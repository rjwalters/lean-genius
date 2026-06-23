# Problem: Hurwitz Theorem — Connection to Exceptional Lie Groups

**Slug**: hurwitz-theorem-oq-04
**Created**: 2026-04-23
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

What is the connection between Hurwitz's theorem (the only normed division algebras over ℝ
are ℝ, ℂ, ℍ, 𝕆 in dimensions 1, 2, 4, 8) and the exceptional Lie groups (G₂, F₄, E₆, E₇, E₈),
and can any part of this connection be formalized in Lean 4?

Concretely: G₂ = Aut(𝕆) (automorphisms of the octonions), F₄ relates to the octonionic
projective plane, and E₆, E₇, E₈ arise from the "magic square" (Freudenthal-Tits) construction
using normed division algebras. Can the definition G₂ = Aut(𝕆) be stated and the
connection to Hurwitz's classification formalized?

### Plain Language

Hurwitz's theorem classifies the normed division algebras: only ℝ (dim 1), ℂ (dim 2),
quaternions ℍ (dim 4), and octonions 𝕆 (dim 8) exist. The octonions, being non-associative,
have a surprisingly rich symmetry group. The automorphism group of 𝕆 is the exceptional
Lie group G₂ (a 14-dimensional compact Lie group). This is one of the deepest connections
in mathematics, linking the "accident" of 8-dimensional normed algebras to exceptional symmetry.

### Why This Matters

This connection is part of the "exceptional mathematics" program. The fact that G₂ = Aut(𝕆)
is a precise theorem with known proofs. Formalizing even the definition/statement would be
a significant contribution, and G₂ currently has minimal Mathlib representation.

## Known Results

### What's Already Proven

- `hurwitz-theorem`: Full formalization of Hurwitz's theorem (ℝ, ℂ, ℍ, 𝕆 are the only normed division algebras)
- The octonion identity for n=8 is constructively proved via Cayley-Dickson

### What's Still Open

- Formal definition of G₂ as Aut(𝕆) in Lean 4
- Formalization of the Freudenthal-Tits magic square construction
- Connection between G₂ compactness and octonion properties

### Our Goal

Minimally: state the theorem `G₂ ≅ Aut(𝕆)` as a formal Lean declaration using the existing
`Octonion` type in Mathlib, and assess what infrastructure exists for proving it.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `hurwitz-theorem` | Parent proof; octonion and Hurwitz classification formalized | NormedAlgebra, Octonion |
| `hurwitz-theorem-oq-03` | Clifford algebra approach to Hurwitz | CliffordAlgebra |

## Initial Thoughts

### Potential Approaches

1. **Definition-first**: Define G₂ = Aut(𝕆) as the group of ℝ-algebra automorphisms of
   `Octonion ℝ`, then state the isomorphism with the classical G₂ as a formal sorry.
   - Why it might work: Mathlib has `AlgEquiv` and `Aut` infrastructure; `Octonion ℝ` exists
   - Risk: Classical G₂ may not be defined in Mathlib yet

2. **Automorphism characterization**: Prove that every automorphism of 𝕆 preserves the
   norm (hence is in SO(8)), and that Aut(𝕆) is a compact 14-dimensional Lie group.
   - Why it might work: Norm preservation follows from algebra map properties
   - Risk: Lie group structure on Aut(𝕆) requires significant infrastructure

### Key Difficulties

- `LieGroup`, `ExceptionalLieGroup` — these are not well-developed in Mathlib
- The classification of G₂ as a simple Lie group of dimension 14 requires non-trivial Lie theory
- Most Mathlib Lie group work is for matrix groups, not automorphism groups of algebras

### What Would a Proof Need?

- Key lemma 1: `MulEquiv.ofAlgEquiv` — automorphisms of `Octonion ℝ` form a group
- Key lemma 2: Norm-preserving property of octonionic automorphisms
- Technical: `Mathlib.Algebra.Octonion`, `Mathlib.GroupTheory.Aut`, `Mathlib.Analysis.SpecialFunctions.LieGroups`

## Tractability Assessment

**Difficulty**: High (formalization of the connection) / Medium (stating the theorem)

**Justification**:
- Fully proving G₂ ≅ Aut(𝕆) is hard: requires Lie theory not in Mathlib
- Stating the theorem with sorry and identifying the gap is tractable
- Partial results (automorphisms preserve norm, Aut(𝕆) is a group) are tractable

## Metadata

```yaml
tags:
  - algebra
  - lie-groups
  - hurwitz
  - composition-algebras
  - exceptional
related_proofs:
  - hurwitz-theorem
  - hurwitz-theorem-oq-03
difficulty: high
source: gallery-gap
created: 2026-04-23
```

**Significance**: 7/10
**Tractability**: 4/10
