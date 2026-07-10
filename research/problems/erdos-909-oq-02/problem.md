# Problem: What is dim(S_n^k) for the Anderson-Keisler space S_n when k > 2?

**Slug**: erdos-909-oq-02
**Created**: 2026-07-09T00:00:00Z
**Status**: Active
**Source**: proof-suggestion (open question spun off from `erdos-909`)

## Problem Statement

### Formal Statement

$$
\textsf{Open question (extension) extending Erdős Problem #909: Dimension of Product Spaces.}
$$

Precise formalization is the first task for the Researcher; the mathematical
content is stated below.

### Plain Language

What is dim(S_n^k) for the Anderson-Keisler space S_n when k > 2? Does dim(S_n^k) = n for all k?

### Why This Matters

This is a challenging extension question arising directly from the completed gallery
entry `erdos-909` ("Erdős Problem #909: Dimension of Product Spaces").
Resolving it extends the reach of an already-formalized result and clarifies how
far the parent proof's techniques generalize.

## Known Results

### What's Already Proven

- The parent result `erdos-909` is fully formalized in the gallery and provides the base case and available lemmas.

### What's Still Open

- The precise question stated above; no formalization of it currently exists in the gallery.

### Our Goal

Produce a Lean 4 formalization (or a rigorous obstruction/negative result) for the
question above, reusing the parent entry's definitions and lemmas wherever possible.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-909` | Parent / originating gallery entry | see entry meta.json |

## Initial Thoughts

### Potential Approaches

1. **Reuse the parent construction.** Start from the definitions and key lemmas of the
   parent entry and attempt to push them through the generalized hypotheses.
2. **Search Mathlib for supporting theory** covering the tags: erdos, topology, dimension-theory, product-spaces, solved.

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
- Modules relevant to the tags erdos, topology, dimension-theory, product-spaces, solved — to be surveyed during ORIENT.

## Metadata

```yaml
tags:
  - erdos
  - topology
  - dimension-theory
  - product-spaces
  - solved
related_proofs:
  - erdos-909
difficulty: challenging
source: proof-suggestion
created: 2026-07-09T00:00:00Z
```
