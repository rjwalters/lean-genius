# Problem: Ultra-Log-Concavity of Binomial Coefficients

**Slug**: newton-inductive-step-oq-02
**Created**: 2026-03-30
**Status**: Active
**Source**: gallery-gap (open question from newton-inductive-step proof)

## Problem Statement

### Formal Statement

$$
\text{For fixed } m \geq 0, \text{ prove } \binom{m}{k}^4 \geq \binom{m}{k-1}^2 \cdot \binom{m}{k+1}^2 \text{ for all } 1 \leq k \leq m-1.
$$

### Plain Language

Prove that the squared binomial coefficients $\binom{m}{k}^2$ form a log-concave sequence in $k$ (ultra-log-concavity). This strengthens the ordinary log-concavity of binomial coefficients proved in the parent newton-inductive-step proof.

### Why This Matters

Ultra-log-concavity connects combinatorics to probability (negative dependence), algebra (real-rootedness), and optimization (log-concave distributions).

## Known Results

### What's Already Proven

- `newton-inductive-step`: Inductive step for Newton's log-concavity (verified, 0 axioms)
- Mathlib has `Nat.choose` and basic binomial coefficient identities

### Our Goal

Formalize ultra-log-concavity of binomial coefficients in Lean 4.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| newton-inductive-step | Direct parent, verified | Induction, polynomial log-concavity |
| binomial-theorem | Binomial coefficient foundations | Nat.choose identities |

## Suggested First Steps

1. Check Mathlib for ratio monotonicity: $\binom{m}{k}/\binom{m}{k-1} = (m-k+1)/k$ decreasing
2. Derive ultra-log-concavity from ratio monotonicity squared
3. Formalize as a standalone theorem extending the parent proof

## Metadata

```yaml
tags: [combinatorics, inequalities, log-concavity, binomial-coefficients]
related_proofs: [newton-inductive-step, binomial-theorem]
difficulty: medium
source: gallery-gap
created: 2026-03-30
```

**Significance**: 7/10
**Tractability**: 6/10
