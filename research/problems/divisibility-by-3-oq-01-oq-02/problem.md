# Problem: Extend truncation coverage beyond 19 (23, 29, 31, 37, 41, 43)

**Slug**: divisibility-by-3-oq-01-oq-02
**Created**: 2026-06-10
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
Extend truncation coverage beyond 19 (23, 29, 31, 37, 41, 43)
$$

### Plain Language

This open question arises from the gallery proof `divisibility-by-3-oq-01` (Formal Divisibility Rules for Various Bases and Moduli). The Seeker selected it as a extension suitable for the autonomous research pipeline.

The specific question: Extend truncation coverage beyond 19 (23, 29, 31, 37, 41, 43)

### Why This Matters

Significance score 5/10 — the problem extends a verified gallery proof in a concrete direction. Closing it would add a extension-style follow-up to the gallery corpus and exercise machinery from the parent entry.

## Known Results

### What's Already Proven

- Parent proof `divisibility-by-3-oq-01` — provides the base theorem and its Mathlib infrastructure
- Sibling open questions on the same gallery entry — see `src/data/proofs/divisibility-by-3/meta.json` `conclusion.openQuestions`

### What's Still Open

- The question stated above, as a extension of the parent result
- Quantitative / constructive refinements that the Researcher may identify during OBSERVE

### Our Goal

Formulate the question as a Lean 4 theorem aligned with the parent entry's namespace, identify the Mathlib lemmas that close the gap, and either prove it or carve out a precise sub-claim that is tractable.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| divisibility-by-3 | Gallery root containing the open question | Parent definitions, Mathlib infrastructure used by the proof |
| divisibility-by-3-oq-01 | Immediate source of this open question | Source proof techniques carried over |

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
- Seeker-assigned tractability score 6/10 reflects a likely-tractable direct extension
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
  - divisibility
  - modular-arithmetic
  - extension
  - comprehensive
  - seeker-selected
related_proofs:
  - divisibility-by-3-oq-01
  - divisibility-by-3
difficulty: medium
source: gallery-gap
created: 2026-06-10
significance: 5
tractability: 6
tier: B
category: extension
```
