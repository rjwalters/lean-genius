# Problem: Generalize to ℝⁿ and ℂⁿ: the set of points with at least one algebraic coordi...

**Slug**: algebraic-numbers-countable-oq-07-oq-03
**Status**: Active
**Source**: gallery-gap
**Parent proof**: algebraic-numbers-countable-oq-07
**Significance**: 6/10 | **Tractability**: 7/10 | **Tier**: B

## Problem Statement

### Formal Statement

$$
\text{In } \mathbb{R}^n:\ \{x : \exists i,\ x_i \in \overline{\mathbb{Q}}\} \text{ is Lebesgue-null, and } \overline{\mathbb{Q}}^n \text{ is countable (hence null).}
$$

### Plain Language

Lift the parent's 1-dimensional result (the algebraic reals are countable, hence Lebesgue-null) to R^n and C^n: the set of points with at least one algebraic coordinate is null, and the fully-algebraic points are countable. Almost every point has all coordinates transcendental and algebraically independent.

### Why This Matters

Grounded, self-contained generalization off a completed, verified gallery entry (algebraic-numbers-countable-oq-07). Extends an established result along a concrete axis with existing Mathlib support, keeping it a tractable 0-axiom target rather than an open-ended conjecture.

## Known Results

### What's Already Proven

- Parent algebraic-numbers-countable-oq-07 (1-D null / countable)
- Mathlib `Set.Countable.measure_zero`, `MeasureTheory.measure_pi`
- Fubini / product-measure null sets: coordinate slices null ⇒ union null

## Suggested First Steps

1. Read the parent proof `algebraic-numbers-countable-oq-07` and identify the exact lemma to generalize.
2. Survey Mathlib for the supporting API listed above (Scout during ORIENT).
3. State the generalized theorem and attempt the direct lifting; keep it 0-axiom.

## Source Description

Generalize to ℝⁿ and ℂⁿ: the set of points with at least one algebraic coordinate is null in ℝⁿ, and the algebraic points (all coordinates algebraic) are countable hence null. State and prove the n-dimensional version, where 'almost every point has all coordinates transcendental and algebraically independent'.
