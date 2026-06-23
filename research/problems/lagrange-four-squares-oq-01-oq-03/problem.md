# Problem: What is the exact count of four-square representations of n, and can the Jacobi four-square formula 

**Slug**: lagrange-four-squares-oq-01-oq-03
**Created**: 2026-06-15
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
What is the exact count of four-square representations of n, and can the Jacobi four-square formula r₄(n) = 8·Σ_{4∤d} d be formalized?
$$

### Plain Language

This open question arises from the gallery proof `lagrange-four-squares-oq-01` (Computational Complexity of Four-Square Representations (OQ-01)). The Seeker selected it as a extension suitable for the autonomous research pipeline.

The specific question: What is the exact count of four-square representations of n, and can the Jacobi four-square formula r₄(n) = 8·Σ_{4∤d} d be formalized?

### Why This Matters

Significance score 7/10 — the problem extends a verified gallery proof in a concrete direction. Closing it would add a extension-style follow-up to the gallery corpus and exercise machinery from the parent entry.

## Known Results

### What's Already Proven

- Parent proof `lagrange-four-squares-oq-01` — provides the base theorem and its Mathlib infrastructure
- Sibling open questions on the same gallery entry — see `src/data/proofs/lagrange-four-squares/meta.json` `conclusion.openQuestions`

### What's Still Open

- The question stated above, as a extension of the parent result
- Quantitative / constructive refinements that the Researcher may identify during OBSERVE

### Our Goal

Formulate the question as a Lean 4 theorem aligned with the parent entry's namespace, identify the Mathlib lemmas that close the gap, and either prove it or carve out a precise sub-claim that is tractable.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| lagrange-four-squares | Gallery root containing the open question | Parent definitions, Mathlib infrastructure used by the proof |
| lagrange-four-squares-oq-01 | Immediate source of this open question | Source proof techniques carried over |

## Initial Thoughts

### Potential Approaches

1. **Direct Mathlib search**: Survey Mathlib for definitions and lemmas matching the question's keywords; many gallery open questions reduce to wiring an existing Mathlib API.
   - Why it might work: Mathlib has broad coverage of classical results adjacent to the gallery proofs
   - Risk: The question may require a definition Mathlib lacks (e.g. a specialized object), in which case the work shifts to defining it

2. **Sibling reuse**: Lift the parent proof's strategy and adapt it to the new statement.
   - Why it might work: The original proof author already structured the gallery entry to make this kind of extension feasible
   - Risk: The sibling lemmas may not generalize cleanly; bookkeeping can dominate

### Key Difficulties

- Need to identify the precise Lean 4 statement; the natural-language description leaves room for interpretation
- Mathlib coverage may be partial — the OBSERVE phase must check which pieces exist

### What Would a Proof Need?

- Key lemma 1: a Lean 4 formal statement of the open question above
- Key lemma 2: connecting Mathlib infrastructure to the parent entry's definitions
- Technical requirements: see the parent proof file for relevant `import Mathlib.*` statements

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Seeker-assigned tractability score 5/10 reflects a likely-tractable direct extension
- Parent entry is verified, so the surrounding Lean infrastructure is in place
- Mathlib coverage of adjacent material is non-trivial; survey by the Scout in ORIENT is advisable

**Estimated Effort**:
- Exploration: 4-8 hours during OBSERVE/ORIENT
- If tractable: 1-3 days for a clean theorem statement plus proof
- If hard: weeks; consider carving a narrower sub-question

## References

### Papers
- See the parent gallery entry's `references` array for citations to the originating literature

### Online Resources
- https://github.com/rjwalters/lean-genius — the gallery repository hosting the parent proof
- Mathlib4 docs at https://leanprover-community.github.io/mathlib4_docs/ — for searching Mathlib namespaces relevant to the keywords below

### Mathlib
- Relevant Mathlib modules will surface during ORIENT; start from the parent proof's existing imports

## Metadata

```yaml
tags:
  - four-squares
  - gallery-extracted
  - lagrange-theorem
  - number-theory
  - quadratic-forms
  - seeker-selected
  - sums-of-squares
related_proofs:
  - lagrange-four-squares-oq-01
  - lagrange-four-squares
difficulty: medium
source: gallery-gap
created: 2026-06-15
significance: 7
tractability: 5
tier: B
category: extension
```

**Significance**: 7/10
**Tractability**: 5/10
