# Problem: Generalize BSC Capacity to Symmetric Channels

**Slug**: shannon-channel-coding-oq-02-oq-04
**Created**: 2026-04-12
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Plain Language

Extend the Binary Symmetric Channel capacity proof to general symmetric discrete memoryless channels.

### Why This Matters

Bridges the gap between the specific BSC result and the general channel coding theorem.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| shannon-channel-coding | Parent proof — foundation for this extension |

## Initial Thoughts

### Potential Approach

Start from existing BSC capacity proof. Define symmetric DMC in Lean. Prove capacity formula via input symmetry argument.

### Key Difficulties

- Identifying which Mathlib lemmas are needed
- Bridging the gap between the known result and the extension

## Tractability Assessment

**Difficulty**: Medium
**Category**: generalization

## Metadata

```yaml
tags: ["information-theory", "analysis", "probability", "coding-theory", "channel-capacity"]
related_proofs: ["shannon-channel-coding-oq-02"]
difficulty: medium
source: gallery-gap
created: 2026-04-12
```
