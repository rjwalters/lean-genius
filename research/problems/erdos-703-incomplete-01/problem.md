# Problem: Forbidden r-Intersection Families

**Slug**: erdos-703-incomplete-01
**Created**: 2026-04-03T05:22:49
**Updated**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The problem is sourced from the gallery proof `erdos-703`.

**Gallery proof status**: 1 sorry(s), 2 axiom(s)

**Problem Type**: COMPLETION

### Open Question

Complete the formalization of Forbidden r-Intersection Families by resolving 1 sorry statement(s)

### Plain Language

Define T(n,r) as the maximum family size avoiding r-intersection. Is T(n,r) < (2-δ)^n for εn < r < (1/2-ε)n? SOLVED: YES (Frankl-Rödl 1987). Exact values known for small r (Frankl-Füredi 1984).

## Gallery Context

- **Gallery Entry**: `erdos-703`
- **Title**: Forbidden r-Intersection Families
- **Tags**: erdos, combinatorics, set-families, extremal, intersection-problems
- **Sorries**: 1
- **Axioms**: 2

## Mathematical Background

See gallery entry for mathematical background.

## Research Approach

### For OBSERVE Phase
1. Read the gallery proof at `src/data/proofs/erdos-703/meta.json`
2. Study the Lean source file
3. Understand existing proof structure and the sorry statement(s)

### For ORIENT Phase
4. Research relevant Mathlib tactics and lemmas
5. Check for related gallery proofs

### For DECIDE Phase
6. Design a proof strategy

### For ACT Phase
7. Implement the proof
8. Verify with docker-build.sh

## Significance: 7/10
## Tractability: 5/10 (challenging)
