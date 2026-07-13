# Problem: Extend to sums of three and four squares (Legendre's and Lagrange's theorems)...

**Slug**: pythagorean-triples-oq-04-oq-04
**Status**: Active
**Source**: gallery-gap
**Parent proof**: pythagorean-triples-oq-04
**Significance**: 6/10 | **Tractability**: 5/10 | **Tier**: B

## Problem Statement

### Formal Statement

$$
n=a^2+b^2+c^2 \text{ (Legendre: iff } n \ne 4^k(8m+7)) \quad\text{and}\quad n=a^2+b^2+c^2+d^2 \text{ (Lagrange: always).}
$$

### Plain Language

Extend the parent's sum-of-two-squares analysis to sums of three squares (Legendre's three-square theorem, with the 4^k(8m+7) obstruction) and four squares (Lagrange's four-square theorem, no obstruction), contrasting the obstruction patterns. Mathlib already has the four-square theorem (`Nat.sum_four_squares`); the three-square case is the harder open direction.

### Why This Matters

Grounded, self-contained generalization off a completed, verified gallery entry (pythagorean-triples-oq-04). Extends an established result along a concrete axis with existing Mathlib support, keeping it a tractable 0-axiom target rather than an open-ended conjecture.

## Known Results

### What's Already Proven

- Parent pythagorean-triples-oq-04 (sum of two squares)
- Mathlib `Nat.sum_four_squares` (Lagrange)
- Legendre three-square theorem (not yet in Mathlib) — obstruction 4^k(8m+7)

## Suggested First Steps

1. Read the parent proof `pythagorean-triples-oq-04` and identify the exact lemma to generalize.
2. Survey Mathlib for the supporting API listed above (Scout during ORIENT).
3. State the generalized theorem and attempt the direct lifting; keep it 0-axiom.

## Source Description

Extend to sums of three and four squares (Legendre's and Lagrange's theorems) and contrast the obstruction patterns
