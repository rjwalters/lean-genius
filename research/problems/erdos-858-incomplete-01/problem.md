# Problem: Erdős Problem #858: Avoiding Multiplicative Relations with Large Prime Factors

**Slug**: erdos-858-incomplete-01
**Created**: 2026-04-03T05:22:49
**Updated**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The problem is sourced from the gallery proof `erdos-858`.

**Gallery proof status**: 1 sorry(s), 1 axiom(s)

**Problem Type**: COMPLETION

### Open Question

Complete the formalization of Erdős Problem #858: Avoiding Multiplicative Relations with Large Prime Factors by resolving 1 sorry statement(s)

### Plain Language

For A ⊆ {1,...,N} with no at=b where a,b ∈ A and smallest prime factor of t > a, estimate max (1/log N) Σ_{n∈A} 1/n. SOLVED: The maximum is o(1) as N → ∞, proved by Alexander (1966) and Erdős-Sárközi-Szemerédi (1968).

## Gallery Context

- **Gallery Entry**: `erdos-858`
- **Title**: Erdős Problem #858: Avoiding Multiplicative Relations with Large Prime Factors
- **Tags**: erdos, number-theory, primitive-sets, multiplicative-structure, density
- **Sorries**: 1
- **Axioms**: 1

## Mathematical Background

See gallery entry for mathematical background.

## Research Approach

### For OBSERVE Phase
1. Read the gallery proof at `src/data/proofs/erdos-858/meta.json`
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
