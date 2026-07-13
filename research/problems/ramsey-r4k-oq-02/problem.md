# Problem: Can the exact Ramsey numbers $R(4,3) = 9$, $R(4,4) = 18$, $R(4,5) = 25$ be ve...

**Slug**: ramsey-r4k-oq-02
**Created**: 2026-06-09
**Status**: Active
**Source**: gallery-open-question

## Problem Statement

### Formal Statement

The question extracted from the gallery entry `ramsey-r4k` (Ramsey R(4,k): Structural Bounds and Cubic Growth):

> Can the exact Ramsey numbers $R(4,3) = 9$, $R(4,4) = 18$, $R(4,5) = 25$ be verified in Lean 4? This requires either SAT-solver integration (to verify the extremal colorings on $n-1$ vertices) or an inductive combinatorial argument.

### Plain Language

Extracted as a `extension` follow-up to the gallery proof `ramsey-r4k` and classified as `challenging` based on the gallery extractor heuristics. The full prose statement above describes what the Researcher should explore.

### Why This Matters

This question expands the gallery proof `ramsey-r4k` (Ramsey R(4,k): Structural Bounds and Cubic Growth) by addressing an explicit follow-up the proof itself raised. Resolving it would tighten or generalize an existing gallery result.

## Known Results

### What's Already Proven

- Source gallery proof: `ramsey-r4k` is the parent entry and contains the toolkit and statements this question extends.
- Mathlib provides ambient definitions and lemmas referenced by the source proof.

### What's Still Open

- The exact question above, as stated by the source gallery entry under `openQuestions`.
- Any auxiliary lemmas the Researcher discovers during OBSERVE.

### Our Goal

Make concrete progress on the stated question: either produce a Lean proof, refine the statement into a falsifiable sub-goal, or surface specific obstructions that point at the next experiment.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `ramsey-r4k` | Related gallery proof | — |


## Initial Thoughts

### Potential Approaches

1. **Mirror the source proof's techniques**: re-read `ramsey-r4k`'s Lean file and adapt its lemmas to the new question.
   - Why it might work: the proof's authors anticipated this extension when writing `openQuestions`.
   - Risk: the new question may require strictly stronger tools.

2. **Search Mathlib for prerequisites**: identify the core Mathlib definitions/lemmas that would be needed and check their availability.
   - Why it might work: many extensions are unlocked by Mathlib additions in the last 6 months.
   - Risk: required lemmas may not yet exist in Mathlib.

### Key Difficulties

- Translating the prose `openQuestion` into a precise Lean statement.
- Identifying which Mathlib API surface to use.

### What Would a Proof Need?

- A precise Lean statement of the question.
- The toolkit currently used by the source proof, adapted to the new setting.
- Possibly new auxiliary lemmas not yet in Mathlib.

## Tractability Assessment

**Difficulty**: Challenging

**Justification**:
- Classified `challenging` by the gallery extractor.
- Source proof exists and provides scaffolding.
- Category `extension` typically requires re-using established techniques.

**Estimated Effort**:
- Exploration: days
- If tractable: 1–2 weeks
- If hard: unknown

## References

### Papers

- See the source proof `ramsey-r4k` for primary citations.

### Online Resources

- Gallery entry: `src/data/proofs/ramsey-r4k/`

### Mathlib

- Whatever modules the source proof imports.

## Metadata

```yaml
tags:
  - combinatorics
  - ramsey-theory
  - graph-theory
  - probabilistic-method
  - number-theory
  - upper-bounds
related_proofs:
  - ramsey-r4k
difficulty: challenging
source: gallery-open-question
created: 2026-06-09
```
