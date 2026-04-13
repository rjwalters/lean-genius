# Problem: Taylor's Theorem with Lagrange Remainder

**Slug**: mean-value-theorem-oq-02-oq-01
**Created**: 2026-04-03T05:22:49
**Updated**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The problem is sourced from the gallery proof `mean-value-theorem-oq-02`.

**Gallery proof status**: 0 sorry(s), 1 axiom(s)

**Problem Type**: EXTENSION

### Open Question

Can the axiom `taylor_lagrange_remainder` be proved from Mathlib's integral form? The key missing lemma is the MVT for integrals applied to $h(t) = (b-t)^n / n!$ and $g(t) = f^{(n+1)}(t)$ on $[a,b]$.

### Plain Language

Formalizes the higher-order Mean Value Theorem (Taylor's theorem with Lagrange remainder). Defines the Taylor polynomial, axiomatizes the Lagrange remainder, proves MVT is the n=0 case, and derives the second-order Taylor expansion.

## Gallery Context

- **Gallery Entry**: `mean-value-theorem-oq-02`
- **Title**: Taylor's Theorem with Lagrange Remainder
- **Tags**: calculus, taylor-theorem, mean-value-theorem, analysis, research
- **Sorries**: 0
- **Axioms**: 1

## Mathematical Background

See gallery entry for mathematical background.

## Research Approach

### For OBSERVE Phase
1. Read the gallery proof at `src/data/proofs/mean-value-theorem-oq-02/meta.json`
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
