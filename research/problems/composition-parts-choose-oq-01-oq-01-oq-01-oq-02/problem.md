# Problem: Can the higher moments — the third moment / skewness, or the full moment gene...

**Slug**: composition-parts-choose-oq-01-oq-01-oq-01-oq-02
**Status**: Active
**Source**: gallery-gap
**Parent proof**: composition-parts-choose-oq-01-oq-01-oq-01
**Significance**: 5/10 | **Tractability**: 7/10 | **Tier**: B

## Problem Statement

### Formal Statement

$$
\text{Derive } \mathbb{E}[K^r] \text{ and the MGF of the part-count } K \sim \mathrm{Binomial}(n-1, \tfrac12) \text{ from } \sum_k k^r \binom{m}{k}.
$$

### Plain Language

The number of parts in a random composition of n is Binomial(n-1, 1/2)-distributed. The parent derived mean and variance via an absorption-rule reduction of sum_k k^r C(m,k). Extend the same reduction to higher moments (third moment / skewness) and ideally the full moment generating function.

### Why This Matters

Grounded, self-contained generalization off a completed, verified gallery entry (composition-parts-choose-oq-01-oq-01-oq-01). Extends an established result along a concrete axis with existing Mathlib support, keeping it a tractable 0-axiom target rather than an open-ended conjecture.

## Known Results

### What's Already Proven

- Parent composition-parts-choose-oq-01-oq-01-oq-01 (mean & variance via absorption rule)
- Mathlib `Nat.succ_mul_choose_eq` / `Finset.sum_range_choose`
- Binomial moment identities

## Suggested First Steps

1. Read the parent proof `composition-parts-choose-oq-01-oq-01-oq-01` and identify the exact lemma to generalize.
2. Survey Mathlib for the supporting API listed above (Scout during ORIENT).
3. State the generalized theorem and attempt the direct lifting; keep it 0-axiom.

## Source Description

Can the higher moments — the third moment / skewness, or the full moment generating function of the $\mathrm{Binomial}(n-1, 1/2)$ part-count — be derived from the same absorption-rule reduction applied to $\sum_k k^r\binom{m}{k}$?
