# Problem: Does the 2-torsion bound extend to characterize when the Sylow 2-subgroup of ...

**Slug**: gauss-wilson-non-cyclic-oq-02
**Created**: 2026-06-10
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
Does the 2-torsion bound extend to characterize when the Sylow 2-subgroup of (ZMod n)× is elementary abelian versus cyclic?
$$

### Plain Language

This open question arises from the gallery proof `gauss-wilson-non-cyclic` (Non-Cyclic 2-Torsion in (ZMod n)×). The Seeker selected it as a generalization suitable for the autonomous research pipeline.

The specific question: Does the 2-torsion bound extend to characterize when the Sylow 2-subgroup of (ZMod n)× is elementary abelian versus cyclic?

### Why This Matters

Significance score 6/10 — the problem extends a verified gallery proof in a concrete direction. Closing it would add a generalization-style follow-up to the gallery corpus and exercise machinery from the parent entry.

## Known Results

### What's Already Proven

- Parent proof `gauss-wilson-non-cyclic` — provides the base theorem and its Mathlib infrastructure
- Sibling open questions on the same gallery entry — see `src/data/proofs/gauss-wilson-non-cyclic/meta.json` `conclusion.openQuestions`

### What's Still Open

- The question stated above, as a generalization of the parent result
- Quantitative / constructive refinements that the Researcher may identify during OBSERVE

### Our Goal

Formulate the question as a Lean 4 theorem aligned with the parent entry's namespace, identify the Mathlib lemmas that close the gap, and either prove it or carve out a precise sub-claim that is tractable.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| gauss-wilson-non-cyclic | Gallery root containing the open question | Parent definitions, Mathlib infrastructure used by the proof |
| gauss-wilson-non-cyclic | Immediate source of this open question | Source proof techniques carried over |

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
  - number-theory
  - group-theory
  - cyclic-groups
  - zmod
  - wilson-gauss
  - seeker-selected
related_proofs:
  - gauss-wilson-non-cyclic
  - gauss-wilson-non-cyclic
difficulty: medium
source: gallery-gap
created: 2026-06-10
significance: 6
tractability: 5
tier: B
category: generalization
```
