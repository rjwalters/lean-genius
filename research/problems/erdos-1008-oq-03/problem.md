# Problem: What happens for odd cycle-freeness (C₅, C₇, ...) instead of C₄?

**Slug**: erdos-1008-oq-03
**Created**: 2026-07-09T00:00:00Z
**Status**: Active
**Source**: proof-suggestion (open question spun off from `erdos-1008`)

## Problem Statement

### Formal Statement

$$
\textsf{Open question (extension) extending Erdős Problem #1008: C₄-Free Subgraphs.}
$$

Precise formalization is the first task for the Researcher; the mathematical
content is stated below.

### Plain Language

What happens for odd cycle-freeness (C₅, C₇, ...) instead of C₄?

### Why This Matters

This is a challenging extension question arising directly from the completed gallery
entry `erdos-1008` ("Erdős Problem #1008: C₄-Free Subgraphs").
Resolving it extends the reach of an already-formalized result and clarifies how
far the parent proof's techniques generalize.

## Known Results

### What's Already Proven

- The parent result `erdos-1008` is fully formalized in the gallery and provides the base case and available lemmas.

### What's Still Open

- The precise question stated above; no formalization of it currently exists in the gallery.

### Our Goal

Produce a Lean 4 formalization (or a rigorous obstruction/negative result) for the
question above, reusing the parent entry's definitions and lemmas wherever possible.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-1008` | Parent / originating gallery entry | see entry meta.json |

## Initial Thoughts

### Potential Approaches

1. **Reuse the parent construction.** Start from the definitions and key lemmas of the
   parent entry and attempt to push them through the generalized hypotheses.
2. **Search Mathlib for supporting theory** covering the tags: erdos, graph-theory, extremal, cycles, subgraphs, zarankiewicz.

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
- Modules relevant to the tags erdos, graph-theory, extremal, cycles, subgraphs, zarankiewicz — to be surveyed during ORIENT.

## Metadata

```yaml
tags:
  - erdos
  - graph-theory
  - extremal
  - cycles
  - subgraphs
  - zarankiewicz
related_proofs:
  - erdos-1008
difficulty: challenging
source: proof-suggestion
created: 2026-07-09T00:00:00Z
```
