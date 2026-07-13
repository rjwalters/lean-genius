# Erdős Problem #305: Maximum Denominator in Egyptian Fraction Representations

**Lean file**: `proofs/Proofs/Erdos305Problem.lean`
**Sorries**: 1
**Status**: available
**Tier**: B | **Significance**: 7/10 | **Tractability**: 4/10

## Problem Statement

Erdős #305: Let $D(b)$ be the maximum denominator when writing $1 = \sum 1/n_i$ with all $n_i \leq b$. How fast does D(b) grow?

**Status**: SOLVED — Yokota (1988) and Liu-Sawhney (2023) proved $D(b) \sim b \cdot (\log b)^{1+o(1)}$.

## The Sorry

```lean
theorem erdos_305_solved : erdos305Conjecture := by
  intro ε hε
  -- The bounds from Yokota/Liu-Sawhney show D(b) ≪ b(log b)^{1+o(1)}
  sorry
```

**Context**: This is proving that the asymptotic bound holds. The conjecture states D(b) grows like b(log b)^{1+o(1)}.

## Mathematical Content

The sorry asks to formalize the Yokota/Liu-Sawhney result. This is a deep number theory result involving Egyptian fractions. The current Lean file likely has a stub asserting the result via axiom or provides the bound structure.

## Challenge

This requires formalizing a non-trivial analytic number theory result. The sorry may be placeholding a difficult asymptotic argument.

## Approach

1. Read `Erdos305Problem.lean` fully to understand what's already there
2. Check if there's an `axiom` or `sorry` at the definition level
3. If the file has the result structure built, maybe just need to connect the pieces
4. Look for simpler partial results that can be proved (lower bounds, specific cases)

## Key Questions

1. What exactly is `erdos305Conjecture` defined as in this file?
2. Are there intermediate lemmas that just need connecting?
3. Is there a weaker version that's already provable?

## Related Gallery Proof

- `src/data/proofs/erdos-305/` — Erdős Problem #305
- `proofs/Proofs/Erdos305Problem.lean` — file with sorry

## First Steps (OBSERVE phase)

1. Read `Erdos305Problem.lean` fully
2. Understand the definition of `erdos305Conjecture`
3. Look for any lemmas that are already proved and could be combined
4. Check if there's a simpler special case that closes the sorry
