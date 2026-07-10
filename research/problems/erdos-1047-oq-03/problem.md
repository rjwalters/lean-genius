# Problem: What is the minimum degree for a non-convex component with all simple roots?

**Slug**: erdos-1047-oq-03
**Created**: 2026-07-09T00:00:00Z
**Status**: Active
**Source**: proof-suggestion (open question spun off from `erdos-1047`)

## Problem Statement

### Formal Statement

$$
\textsf{Open question (extension) extending Erdős Problem #1047: Convexity of Polynomial Lemniscates.}
$$

Precise formalization is the first task for the Researcher; the mathematical
content is stated below.

### Plain Language

What is the minimum degree for a non-convex component with all simple roots?

### Why This Matters

This is a challenging extension question arising directly from the completed gallery
entry `erdos-1047` ("Erdős Problem #1047: Convexity of Polynomial Lemniscates").
Resolving it extends the reach of an already-formalized result and clarifies how
far the parent proof's techniques generalize.

## Known Results

### What's Already Proven

- The parent result `erdos-1047` is fully formalized in the gallery and provides the base case and available lemmas.

### What's Still Open

- The precise question stated above; no formalization of it currently exists in the gallery.

### Our Goal

Produce a Lean 4 formalization (or a rigorous obstruction/negative result) for the
question above, reusing the parent entry's definitions and lemmas wherever possible.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-1047` | Parent / originating gallery entry | see entry meta.json |

## Initial Thoughts

### Potential Approaches

1. **Reuse the parent construction.** Start from the definitions and key lemmas of the
   parent entry and attempt to push them through the generalized hypotheses.
2. **Search Mathlib for supporting theory** covering the tags: erdos, complex-analysis, polynomials, lemniscates, convexity, counterexample.

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
- Modules relevant to the tags erdos, complex-analysis, polynomials, lemniscates, convexity, counterexample — to be surveyed during ORIENT.

## Metadata

```yaml
tags:
  - erdos
  - complex-analysis
  - polynomials
  - lemniscates
  - convexity
  - counterexample
  - potential-theory
related_proofs:
  - erdos-1047
difficulty: challenging
source: proof-suggestion
created: 2026-07-09T00:00:00Z
```
