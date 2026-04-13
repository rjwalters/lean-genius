# Problem: Pythagorean Triples via Gaussian Integers

**Slug**: pythagorean-triples-oq-02-oq-01
**Created**: 2026-04-03T05:22:49
**Updated**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The problem is sourced from the gallery proof `pythagorean-triples-oq-02`.

**Gallery proof status**: 0 sorry(s), 0 axiom(s)

**Problem Type**: EXTENSION

### Open Question

Can the *classification* of all primitive Pythagorean triples be formalized? Every primitive triple has the form $(m^2-n^2, 2mn, m^2+n^2)$ with $\gcd(m,n)=1$ and $m > n > 0$ with $m \not\equiv n \pmod 2$. This uses the UFD property of $\mathbb{Z}[i]$. Mathlib's `Nat.Coprime` and `PythagoreanTriple.eq_iff` may be relevant.

### Plain Language

Shows that the parametric formula for Pythagorean triples (m²-n², 2mn, m²+n²) is the squaring map in ℤ[i]. Norm multiplicativity gives the Brahmagupta-Fibonacci identity and a product rule for triples. Fully verified, 0 axioms.

## Gallery Context

- **Gallery Entry**: `pythagorean-triples-oq-02`
- **Title**: Pythagorean Triples via Gaussian Integers
- **Tags**: number-theory, gaussian-integers, pythagorean-triples, algebraic, research
- **Sorries**: 0
- **Axioms**: 0

## Mathematical Background

See gallery entry for mathematical background.

## Research Approach

### For OBSERVE Phase
1. Read the gallery proof at `src/data/proofs/pythagorean-triples-oq-02/meta.json`
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
