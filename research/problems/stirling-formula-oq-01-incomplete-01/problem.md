# Problem: Higher-Order Stirling Expansion

**Slug**: stirling-formula-oq-01-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
n! \sim \sqrt{2\pi n}(n/e)^n(1 + 1/(12n) + O(1/n^2))
$$

### Plain Language

Formalize the first correction term in Stirling's series. ShannonEntropySSA.lean has Mathlib's basic Stirling; this extends to higher order. 2 sorries remain.

### Why This Matters

See `src/data/proofs/stirling-formula-oq-01/meta.json` for full context. This is a targeted completion/extension of an existing gallery proof.

## Known Results

### What's Already Proven

- Parent proof `stirling-formula-oq-01` provides the foundation
- sorries to fill: 2 (plus any axioms — check source proof)

### Our Goal

Line 94 sorry: Deep — requires Euler-Maclaurin or careful Wallis product analysis. Line 106 sorry: secondary. Check Mathlib.Analysis.SpecialFunctions.Stirling for hook points.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `stirling-formula-oq-01` | Direct parent — inspect its Lean file for sorry locations |

## Tractability Assessment

**Difficulty**: Challenging

## Metadata

```yaml
tags:
  - analysis
  - stirling
  - asymptotic
  - factorial
related_proofs:
  - stirling-formula-oq-01
difficulty: challenging
source: gallery-gap
created: 2026-04-03
```

**Significance**: 7/10
**Tractability**: 6/10
