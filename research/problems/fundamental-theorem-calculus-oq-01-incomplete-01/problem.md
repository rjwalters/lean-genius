# Problem: FTC Lebesgue Generalization: Complete Proof

**Slug**: fundamental-theorem-calculus-oq-01-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{AC}(f) \Rightarrow f'(x) \text{ exists a.e. and } \int_a^b f' = f(b) - f(a)
$$

### Plain Language

The Lebesgue FTC: absolutely continuous functions are a.e. differentiable and the fundamental theorem holds. 1 sorry + 2 axioms for absolutely continuous function theory not yet in Mathlib.

### Why This Matters

See `src/data/proofs/fundamental-theorem-calculus-oq-01/meta.json` for full context. This is a targeted completion/extension of an existing gallery proof.

## Known Results

### What's Already Proven

- Parent proof `fundamental-theorem-calculus-oq-01` provides the foundation
- sorries to fill: 1 (plus any axioms — check source proof)

### Our Goal

Check Mathlib for AbsolutelyContinuous definition. The sorry (line 224) is for Cantor function construction. May need to use MeasureTheory.BoundedVariation tools.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `fundamental-theorem-calculus-oq-01` | Direct parent — inspect its Lean file for sorry locations |

## Tractability Assessment

**Difficulty**: Challenging

## Metadata

```yaml
tags:
  - analysis
  - lebesgue
  - integration
  - absolutely-continuous
related_proofs:
  - fundamental-theorem-calculus-oq-01
difficulty: challenging
source: gallery-gap
created: 2026-04-03
```

**Significance**: 8/10
**Tractability**: 6/10
