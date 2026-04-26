# Problem: Derangement Ratio Error as Alternating Sum

**Slug**: derangements-oq-03-oq-01-oq-02
**Created**: 2026-04-12
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Plain Language

Express the exact error D(n)/n! - 1/e as a closed-form with sign determined by parity of n.

### Why This Matters

Strengthens the classical 1/e convergence with explicit error terms.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| derangements | Parent proof — foundation for this extension |

## Initial Thoughts

### Potential Approach

Use D(n)/n! = sum (-1)^k/k!. Error is tail of exponential series. Formalize via Finset.sum.

### Key Difficulties

- Identifying which Mathlib lemmas are needed
- Bridging the gap between the known result and the extension

## Tractability Assessment

**Difficulty**: Medium
**Category**: extension

## Metadata

```yaml
tags: ["combinatorics", "analysis", "asymptotics", "probability"]
related_proofs: ["derangements-oq-03-oq-01"]
difficulty: medium
source: gallery-gap
created: 2026-04-12
```

**Significance**: 6/10
**Tractability**: 7/10
