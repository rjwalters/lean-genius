# Problem: Generalize amgm_two_eq_iff to the unweighted n-variable geometric/arithmetic ...

**Slug**: jensen-inequality-oq-01-oq-03
**Status**: Active
**Source**: gallery-gap
**Parent proof**: jensen-inequality-oq-01
**Significance**: 5/10 | **Tractability**: 8/10 | **Tier**: B

## Problem Statement

### Formal Statement

$$
\text{For } x_1,\dots,x_n \ge 0:\quad \sqrt[n]{x_1\cdots x_n} \le \frac{x_1+\cdots+x_n}{n}, \text{ with equality iff } x_1=\cdots=x_n.
$$

### Plain Language

Specialize the parent's weighted AM-GM equality characterization (`weighted_amgm_eq_iff`) to uniform weights 1/n, obtaining the classical unweighted n-variable AM-GM equality case as a direct corollary. The two-variable case `amgm_two_eq_iff` is already proven; this lifts it to arbitrary n.

### Why This Matters

Grounded, self-contained generalization off a completed, verified gallery entry (jensen-inequality-oq-01). Extends an established result along a concrete axis with existing Mathlib support, keeping it a tractable 0-axiom target rather than an open-ended conjecture.

## Known Results

### What's Already Proven

- `weighted_amgm_eq_iff` (parent, jensen-inequality-oq-01)
- `amgm_two_eq_iff` (two-variable base case)
- Mathlib `Real.inner_le_weight_mul_Lp` / `Real.geom_mean_le_arith_mean`

## Suggested First Steps

1. Read the parent proof `jensen-inequality-oq-01` and identify the exact lemma to generalize.
2. Survey Mathlib for the supporting API listed above (Scout during ORIENT).
3. State the generalized theorem and attempt the direct lifting; keep it 0-axiom.

## Source Description

Generalize amgm_two_eq_iff to the unweighted n-variable geometric/arithmetic mean equality case as a direct corollary of weighted_amgm_eq_iff with uniform weights 1/n.
