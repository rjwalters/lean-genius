# Problem: Alteration / Deletion Method

**Slug**: prob-method-alteration
**Created**: 2026-03-21
**Status**: Active
**Source**: marquee-initiative
**Initiative**: Probabilistic Method Library (Phase 1)

## Problem Statement

### Formal Statement

$$
\text{Construct a random object, then deterministically remove violations.}
$$
$$
\text{If the expected number of violations is small, a good object survives.}
$$

### Plain Language

The alteration (deletion) method improves on pure expectation arguments: instead of hoping a random object is already good, we start with a random object and then fix it by removing problematic parts. If few parts are problematic in expectation, the remaining object is still large/useful.

### Why This Matters

This technique is essential for graph coloring bounds, independent set existence, and hypergraph problems. It bridges the gap between "exists in expectation" and "exists concretely" more powerfully than the bare first moment method.

## Dependencies

| Direction | Problem | Relationship |
|-----------|---------|-------------|
| **Depends on** | prob-method-expectation | Uses linearity of expectation |
| **Blocks** | prob-method-applications | Key technique for applications |

## Known Results

### What Needs to Be Built

- Alteration principle: random construction + deterministic fix-up
- Application: independent set in sparse graphs (α(G) ≥ n/(2d) for d-regular)
- Application: property B of hypergraphs
- Application: list coloring bounds

## Tractability Assessment

**Difficulty**: Medium
**Tractability**: 7/10
**Significance**: 8/10

## References

### Papers
- Alon & Spencer - "The Probabilistic Method" Ch. 3

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Basic`
- `Mathlib.Order.Filter.Basic`

## Metadata

```yaml
tags:
  - probabilistic-method
  - combinatorics
  - graph-theory
  - marquee-phase-1
difficulty: medium
source: marquee-initiative
initiative: probabilistic-method-library
created: 2026-03-21
```
