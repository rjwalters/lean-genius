# Problem: Ramsey Theory for Hypergraphs

**Slug**: ramseys-theorem-oq-04-oq-01
**Created**: 2026-04-03T05:22:49
**Updated**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The problem is sourced from the gallery proof `ramseys-theorem-oq-04`.

**Gallery proof status**: 0 sorry(s), 1 axiom(s)

**Problem Type**: EXTENSION

### Open Question

Can the stepping-up lemma be formalized to remove the axiom? It requires well-founded induction on (k, n) and the construction: fix v, define c'(T) = c(T ∪ {v}), apply (k-1)-uniform Ramsey to the induced coloring.

### Plain Language

Extends Ramsey's theorem from graphs (k=2) to k-uniform hypergraphs. The hypergraph Ramsey theorem states that for any k, r, n, sufficiently large sets have monochromatic k-subsets under any r-coloring.

## Gallery Context

- **Gallery Entry**: `ramseys-theorem-oq-04`
- **Title**: Ramsey Theory for Hypergraphs
- **Tags**: combinatorics, graph-theory, ramsey-theory, hypergraphs, classic
- **Sorries**: 0
- **Axioms**: 1

## Mathematical Background

See gallery entry for mathematical background.

## Research Approach

### For OBSERVE Phase
1. Read the gallery proof at `src/data/proofs/ramseys-theorem-oq-04/meta.json`
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
