# Problem: Lift the result to the endomorphism setting (Module.End) rather than concrete matrices, for reuse across the gallery's linear-algebra…

**Slug**: cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-03
**Created**: 2026-07-09T00:00:00Z
**Status**: Active
**Source**: proof-suggestion (open question spun off from `cayley-hamilton-cyclic-vector-all-fields-oq-02`)

## Problem Statement

### Formal Statement

$$
\textsf{Open question (extension) extending Commutant of a Cyclic Matrix is K[M].}
$$

Precise formalization is the first task for the Researcher; the mathematical
content is stated below.

### Plain Language

Lift the result to the endomorphism setting (Module.End) rather than concrete matrices, for reuse across the gallery's linear-algebra entries.

### Why This Matters

This is a challenging extension question arising directly from the completed gallery
entry `cayley-hamilton-cyclic-vector-all-fields-oq-02` ("Commutant of a Cyclic Matrix is K[M]").
Resolving it extends the reach of an already-formalized result and clarifies how
far the parent proof's techniques generalize.

## Known Results

### What's Already Proven

- The parent result `cayley-hamilton-cyclic-vector-all-fields-oq-02` is fully formalized in the gallery and provides the base case and available lemmas.

### What's Still Open

- The precise question stated above; no formalization of it currently exists in the gallery.

### Our Goal

Produce a Lean 4 formalization (or a rigorous obstruction/negative result) for the
question above, reusing the parent entry's definitions and lemmas wherever possible.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `cayley-hamilton-cyclic-vector-all-fields-oq-02` | Parent / originating gallery entry | see entry meta.json |

## Initial Thoughts

### Potential Approaches

1. **Reuse the parent construction.** Start from the definitions and key lemmas of the
   parent entry and attempt to push them through the generalized hypotheses.
2. **Search Mathlib for supporting theory** covering the tags: linear-algebra, matrices, cyclic-vector, cayley-hamilton, minimal-polynomial, nonderogatory.

### Key Difficulties

- Identifying which lemmas from the parent proof survive the generalization.
- Locating (or building) the Mathlib scaffolding the new statement requires.

### What Would a Proof Need?

- A precise Lean statement of the question.
- The parent entry's lemmas, adapted to the new setting.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Categorized as `challenging` in the extracted problem registry.
- A directly related, fully formalized parent proof exists, giving a concrete starting point.

## References

### Mathlib
- Modules relevant to the tags linear-algebra, matrices, cyclic-vector, cayley-hamilton, minimal-polynomial, nonderogatory — to be surveyed during ORIENT.

## Metadata

```yaml
tags:
  - linear-algebra
  - matrices
  - cyclic-vector
  - cayley-hamilton
  - minimal-polynomial
  - nonderogatory
  - commutant
  - centralizer
  - research
  - open-question
related_proofs:
  - cayley-hamilton-cyclic-vector-all-fields-oq-02
difficulty: challenging
source: proof-suggestion
created: 2026-07-09T00:00:00Z
```
