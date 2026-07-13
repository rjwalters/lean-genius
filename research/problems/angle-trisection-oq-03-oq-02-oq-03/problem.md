# Problem: The halvings function is exactly the 2-adic valuation v₂(d)

**Slug**: angle-trisection-oq-03-oq-02-oq-03
**Status**: Active
**Source**: gallery-gap
**Parent proof**: angle-trisection-oq-03-oq-02
**Significance**: 6/10 | **Tractability**: 6/10 | **Tier**: B

## Problem Statement

### Formal Statement

$$
\text{halvings}(d) = v_2(d);\ \text{generalize to } \Theta(\log_p d) \text{ p-adic halvings for each prime } p.
$$

### Plain Language

The parent identified the halvings function with the 2-adic valuation v2(d), giving a Θ(log d) constructibility-complexity bound. Generalize to an arbitrary prime p: counting p-adic halvings requires Θ(log_p d) steps, and connect to a p-adic form of the Gauss–Wantzel condition (d | 2^k · 3 · 5 · 17 · …).

### Why This Matters

Grounded, self-contained generalization off a completed, verified gallery entry (angle-trisection-oq-03-oq-02). Extends an established result along a concrete axis with existing Mathlib support, keeping it a tractable 0-axiom target rather than an open-ended conjecture.

## Known Results

### What's Already Proven

- Parent angle-trisection-oq-03-oq-02 (halvings = v₂(d), Θ(log d))
- Mathlib `padicValNat`, `Nat.factorization`
- Gauss–Wantzel constructibility criterion

## Suggested First Steps

1. Read the parent proof `angle-trisection-oq-03-oq-02` and identify the exact lemma to generalize.
2. Survey Mathlib for the supporting API listed above (Scout during ORIENT).
3. State the generalized theorem and attempt the direct lifting; keep it 0-axiom.

## Source Description

The halvings function is exactly the 2-adic valuation v₂(d). Can the Θ(log d) complexity result be generalized to any prime p — proving that counting p-adic halvings requires Θ(logₚ d) steps — and can this be formalized for the p-adic Gauss-Wantzel condition (d | 2ᵏ · 3 · 5 · 17 · …)?
