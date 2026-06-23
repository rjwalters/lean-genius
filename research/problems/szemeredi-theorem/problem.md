# Problem: Szemerédi's Theorem Statement

**Slug**: szemeredi-theorem
**Created**: 2025-12-31
**Status**: Active
**Source**: feasibility-analysis

## Problem Statement

### Formal Statement

$$
\forall k \geq 1, \forall \delta > 0, \exists N: |A| \geq \delta N \implies A \text{ contains } k\text{-AP}
$$

### Plain Language

For any positive integer k and density δ > 0, there exists N such that every subset of {1,...,N} with at least δN elements contains an arithmetic progression of length k. The k=3 case (Roth's theorem) is already in Mathlib.

### Why This Matters

1. **Foundational combinatorics**: Central result in additive combinatorics
2. **Partial formalization**: k=3 done, general statement missing
3. **Survey value**: Document what's needed for k≥4

## Known Results

### What's Already Proven (in Mathlib)

- **Roth's Theorem (k=3)** — via corners/triangle removal
- **Regularity Lemma** — graph partitions
- **Hales-Jewett** — Van der Waerden follows
- **ThreeAPFree** — k=3 AP-free sets

### What's Still Open

- General k definition (only k=3 defined)
- Hypergraph regularity (needed for k>3)
- Full Szemerédi proof

### Our Goal

1. State full Szemerédi theorem formally
2. Define general k-AP predicate
3. Verify k=3 follows from Roth
4. Document gaps for k≥4

## Tractability Assessment

**Significance**: 7/10
**Tractability**: 5/10

**Justification**:
- Statement is straightforward
- k=3 already done
- k≥4 requires major new machinery

## Metadata

```yaml
tags:
  - combinatorics
  - additive-combinatorics
  - arithmetic-progressions
  - regularity-lemma
difficulty: hard
source: feasibility-analysis
created: 2025-12-31
```
