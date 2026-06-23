# Problem: Formalize Besicovitch''s theorem (1940): $\{\sqrt{a_1}, \ldots, \sqrt{a_n}\}$ ...

**Slug**: sqrt2-plus-sqrt3-irrational-oq-02
**Created**: 2026-06-09
**Status**: Active
**Source**: gallery-open-question

## Problem Statement

### Formal Statement

The question extracted from the gallery entry `sqrt2-plus-sqrt3-irrational` (Irrationality of √2 + √3):

> Formalize Besicovitch's theorem (1940): $\{\sqrt{a_1}, \ldots, \sqrt{a_n}\}$ are linearly independent over $\mathbb{Q}$ when $a_1, \ldots, a_n$ are distinct squarefree positive integers. This would give a complete characterization: $\sum_i r_i \sqrt{a_i} \in \mathbb{Q}$ iff all $r_i = 0$ for $a_i > 1$.

### Plain Language

Extracted as a `extension` follow-up to the gallery proof `sqrt2-plus-sqrt3-irrational` and classified as `challenging` based on the gallery extractor heuristics. The full prose statement above describes what the Researcher should explore.

### Why This Matters

This question expands the gallery proof `sqrt2-plus-sqrt3-irrational` (Irrationality of √2 + √3) by addressing an explicit follow-up the proof itself raised. Resolving it would tighten or generalize an existing gallery result.

## Known Results

### What's Already Proven

- Source gallery proof: `sqrt2-plus-sqrt3-irrational` is the parent entry and contains the toolkit and statements this question extends.
- Mathlib provides ambient definitions and lemmas referenced by the source proof.

### What's Still Open

- The exact question above, as stated by the source gallery entry under `openQuestions`.
- Any auxiliary lemmas the Researcher discovers during OBSERVE.

### Our Goal

Make concrete progress on the stated question: either produce a Lean proof, refine the statement into a falsifiable sub-goal, or surface specific obstructions that point at the next experiment.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `sqrt2-plus-sqrt3-irrational` | Related gallery proof | — |


## Initial Thoughts

### Potential Approaches

1. **Mirror the source proof's techniques**: re-read `sqrt2-plus-sqrt3-irrational`'s Lean file and adapt its lemmas to the new question.
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

- See the source proof `sqrt2-plus-sqrt3-irrational` for primary citations.

### Online Resources

- Gallery entry: `src/data/proofs/sqrt2-plus-sqrt3-irrational/`

### Mathlib

- Whatever modules the source proof imports.

## Metadata

```yaml
tags:
  - irrationality
  - real-analysis
  - square-roots
  - number-theory
related_proofs:
  - sqrt2-plus-sqrt3-irrational
difficulty: challenging
source: gallery-open-question
created: 2026-06-09
```
