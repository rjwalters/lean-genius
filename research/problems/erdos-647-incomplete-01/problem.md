# Problem: Erdős Problem #647: Divisor Function Gap Problem

**Slug**: erdos-647-incomplete-01
**Created**: 2026-04-03T05:22:49
**Updated**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The problem is sourced from the gallery proof `erdos-647`.

**Gallery proof status**: 1 sorry(s), 1 axiom(s)

**Problem Type**: COMPLETION

### Open Question

Complete the formalization of Erdős Problem #647: Divisor Function Gap Problem by resolving 1 sorry statement(s)

### Plain Language

Let τ(n) count divisors of n. Is there n > 24 such that max_{m<n}(m + τ(m)) ≤ n + 2? The case n = 24 works, but Erdős doubted any larger n exists. Prize: £25 (~$44).

## Gallery Context

- **Gallery Entry**: `erdos-647`
- **Title**: Erdős Problem #647: Divisor Function Gap Problem
- **Tags**: erdos, number-theory, divisor-function, highly-composite, open-problem
- **Sorries**: 1
- **Axioms**: 1

## Mathematical Background

See gallery entry for mathematical background.

## Research Approach

### For OBSERVE Phase
1. Read the gallery proof at `src/data/proofs/erdos-647/meta.json`
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
## Tractability: 6/10 (challenging)
