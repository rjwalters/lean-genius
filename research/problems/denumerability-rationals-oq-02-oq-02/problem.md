# Problem: ℝ is the Unique Complete Ordered Field

**Slug**: denumerability-rationals-oq-02-oq-02
**Created**: 2026-04-21T21:54:15+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{Any complete ordered field is isomorphic to } \mathbb{R}
$$

Formally: if $(F, +, \cdot, \leq)$ is a complete ordered field, then there exists a unique ordered field isomorphism $\phi: \mathbb{R} \to F$.

### Plain Language

The real numbers are characterized, up to isomorphism, by being a complete ordered field. Any other structure satisfying these axioms is necessarily isomorphic to ℝ. This is the categorical axiom for the real numbers, analogous to Cantor's categoricity theorem for (ℚ, <).

### Why This Matters

- Underpins the foundation of real analysis
- Explains why Dedekind cuts and Cauchy sequences give "the same" ℝ
- Analogous to Cantor's categoricity of ℚ (the parent proof)
- Key in nonstandard analysis and model theory of ordered fields

## Known Results

### What's Already Proven

- `LinearOrderedField.exists_rat_btwn`: Archimedean property — in Mathlib
- `Real.instLinearOrderedField`: ℝ is a linear ordered field — Mathlib
- `denumerability-rationals-oq-02`: Cantor's categoricity of ℚ — gallery
- `Real.orderIsoRatEmbedding`: embedding of ℚ into Archimedean ordered fields — Mathlib

### What's Still Open

- Formalization of uniqueness: any complete ordered field ≅ ℝ
- The canonical isomorphism construction in Lean 4

### Our Goal

Prove in Lean 4: given `F : Type*` with `[LinearOrderedField F]` and completeness, construct an `F ≃+*o ℝ` (ordered ring isomorphism).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| denumerability-rationals-oq-02 | Direct parent: Cantor's categoricity of ℚ | back-and-forth, DLO |
| denumerability-rationals | Countability of ℚ | countable, enumeration |

## Initial Thoughts

### Potential Approaches

1. **Via density of ℚ and Dedekind completion**:
   - Every Archimedean ordered field embeds in ℝ
   - Show embedding is surjective iff F is Dedekind complete
   - Risk: Surjectivity requires careful LUB handling

2. **Via Mathlib's `Real` as completion of ℚ**:
   - ℝ = Cauchy completion of ℚ; any complete ordered field with dense ℚ ≅ ℝ
   - Use `UniformSpace.Completion` theory
   - Risk: Connecting uniform completion to ordered field structure

3. **Direct construction**:
   - Map r : ℝ to sup {q : ℚ | (q : F) ≤ f} in F
   - Verify this is an ordered field isomorphism
   - Risk: Verification of field axioms

### Key Difficulties

- Finding the right Mathlib typeclass combination for completeness
- The isomorphism must preserve both field operations and order
- Universe polymorphism in Lean 4 may complicate the statement

### What Would a Proof Need?

- Key lemma 1: Every complete ordered field is Archimedean
- Key lemma 2: Every Archimedean ordered field has a unique embedding from ℝ
- Key lemma 3: If F is complete, the embedding ℝ → F is surjective
- Mathlib: `Real.instArchimedean`, `OrderIso`, ordered field isomorphism API

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Classical argument is well-understood
- Mathlib has substantial ordered field and completeness infrastructure
- Challenge is finding the right typeclass hierarchy and API
- Universe polymorphism may complicate the isomorphism statement

**Estimated Effort**:
- Exploration: 4-6 hours
- If tractable: 3-5 days

## References

### Papers
- Enderton, H. "A Mathematical Introduction to Logic" (2001) — categoricity

### Mathlib
- `Mathlib.Data.Real.Basic` — ℝ definition
- `Mathlib.Algebra.Order.Archimedean` — Archimedean fields
- `Mathlib.Topology.Algebra.Order.LiminfLimsup` — completeness

## Metadata

```yaml
tags:
  - real-analysis
  - ordered-fields
  - categoricity
  - foundations
related_proofs:
  - denumerability-rationals-oq-02
  - denumerability-rationals
difficulty: medium
source: gallery-gap
created: 2026-04-21T21:54:15+02:00
```

**Significance**: 7/10
**Tractability**: 7/10
