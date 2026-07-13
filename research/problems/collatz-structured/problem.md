# Problem: Collatz for Structured Values

**Slug**: collatz-structured
**Created**: 2025-12-31
**Status**: Active
**Source**: feasibility-analysis

## Problem Statement

### Formal Statement

$$
\forall n \geq 1: \text{Collatz sequence starting at } 2^n \text{ reaches } 1
$$

### Plain Language

Prove that the Collatz sequence reaches 1 for powers of 2 and other structured starting values. The full Collatz conjecture is unsolved, but specific cases like 2^n are trivially provable (pure halving).

### Why This Matters

1. **Novel formalization**: No existing Collatz definition in Mathlib
2. **Tractable milestones**: Powers of 2, closure properties
3. **Educational value**: Recursion and termination proofs

## Known Results

### What's Already Proven

- Basic nat arithmetic in Mathlib
- Even/Odd predicates
- Well-founded recursion for termination

### What's Still Open

- Full Collatz conjecture — UNSOLVED, not our goal
- 2^n - 1 case — Potentially provable with effort

### Our Goal

1. Define Collatz function in Lean
2. Prove 2^n reaches 1 (n halvings)
3. Prove closure: if n reaches 1, so does 2n
4. Verify small cases computationally

## Tractability Assessment

**Significance**: 4/10
**Tractability**: 9/10

**Justification**:
- Powers of 2 case is trivial (pure halving)
- No existing formalization — novel contribution
- Clear implementation path

## Metadata

```yaml
tags:
  - number-theory
  - collatz
  - iteration
  - termination
difficulty: low
source: feasibility-analysis
created: 2025-12-31
```
