# Problem: Formalize the conditional recoloring: recolor only vertices lying in first-round monochromatic edges, in a fixed (random) order, and…

**Slug**: property-b-first-moment-oq-03-oq-03-oq-01
**Created**: 2026-07-09T00:00:00Z
**Status**: Active
**Source**: proof-suggestion (open question spun off from `property-b-first-moment-oq-03-oq-03`)

## Problem Statement

### Formal Statement

$$
\textsf{Open question (extension) extending Property B: Independent Recoloring Cannot Beat Erdős — the Product-Space Repair Leaves the First-Moment Threshold Invariant.}
$$

Precise formalization is the first task for the Researcher; the mathematical
content is stated below.

### Plain Language

Formalize the conditional recoloring: recolor only vertices lying in first-round monochromatic edges, in a fixed (random) order, and bound the probability that any edge is monochromatic afterwards — the genuine two-stage RS model that this entry shows the product model cannot capture.

### Why This Matters

This is a challenging extension question arising directly from the completed gallery
entry `property-b-first-moment-oq-03-oq-03` ("Property B: Independent Recoloring Cannot Beat Erdős — the Product-Space Repair Leaves the First-Moment Threshold Invariant").
Resolving it extends the reach of an already-formalized result and clarifies how
far the parent proof's techniques generalize.

## Known Results

### What's Already Proven

- The parent result `property-b-first-moment-oq-03-oq-03` is fully formalized in the gallery and provides the base case and available lemmas.

### What's Still Open

- The precise question stated above; no formalization of it currently exists in the gallery.

### Our Goal

Produce a Lean 4 formalization (or a rigorous obstruction/negative result) for the
question above, reusing the parent entry's definitions and lemmas wherever possible.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `property-b-first-moment-oq-03-oq-03` | Parent / originating gallery entry | see entry meta.json |

## Initial Thoughts

### Potential Approaches

1. **Reuse the parent construction.** Start from the definitions and key lemmas of the
   parent entry and attempt to push them through the generalized hypotheses.
2. **Search Mathlib for supporting theory** covering the tags: probabilistic-method, property-b, first-moment, recoloring, radhakrishnan-srinivasan, hypergraph-coloring.

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
- Modules relevant to the tags probabilistic-method, property-b, first-moment, recoloring, radhakrishnan-srinivasan, hypergraph-coloring — to be surveyed during ORIENT.

## Metadata

```yaml
tags:
  - probabilistic-method
  - property-b
  - first-moment
  - recoloring
  - radhakrishnan-srinivasan
  - hypergraph-coloring
  - research
related_proofs:
  - property-b-first-moment-oq-03-oq-03
difficulty: challenging
source: proof-suggestion
created: 2026-07-09T00:00:00Z
```
