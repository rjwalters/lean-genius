# Problem: Sharp LLL Criterion ep(d+1) ≤ 1

**Slug**: prob-method-lovasz-local-oq-02
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $\mathcal{A} = \{A_1, \ldots, A_n\}$ be events where each $A_i$ has probability $\leq p$ and is mutually independent of all but $d$ others. If

$$ep(d+1) \leq 1$$

then $\Pr\left[\bigcap_{i=1}^n \bar{A}_i\right] > 0$.

### Plain Language

The gallery's LLL formalization uses the simplified criterion $p(d+1) \leq 1/3$, which is sufficient but not optimal. The true sharp criterion is $ep(d+1) \leq 1$, where $e \approx 2.718$ is Euler's number. This allows a larger probability $p$ (up to $1/(e(d+1))$ instead of $1/(3(d+1))$) for the same guarantee.

Formalizing this requires: (1) expressing $e$ formally in Lean, and (2) re-deriving the LLL bound using the sharper inequality $(1 - 1/(d+1))^d \leq 1/e$.

### Why This Matters

- The factor-of-$e$ improvement matters in tight applications (e.g., proving $k$-colorability of hypergraphs with fewer colors)
- Establishes the connection between Euler's number and combinatorial probability
- The proof that $ep(d+1) \leq 1$ is optimal (the bound is tight) is a beautiful mathematical fact

## Known Results

### What's Already Proven

- Gallery: LLL with $p(d+1) \leq 1/3$ (prob-method-lovasz-local)
- Mathlib: `Real.exp_one`, `Real.add_one_le_exp : ∀ x : ℝ, x + 1 ≤ Real.exp x`
- Mathlib: `Real.exp_pos`, `Real.exp_one_gt_d9` (e > 2.7...)

### What's Still Open

- Lean proof that $(1 - 1/(d+1))^d \leq 1/e$ for all $d \geq 1$
- Re-derivation of LLL under sharp criterion

### Our Goal

Prove `lll_sharp_criterion`: given $ep \cdot (d+1) \leq 1$ and each event has probability $\leq p$ with dependency degree $\leq d$, then a positive probability avoidance configuration exists.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| prob-method-lovasz-local | Direct predecessor | LLL with simplified criterion |
| prob-method-expectation | Context | Basic probabilistic method |
| basel-problem | e appears | Euler's number connections |

## Initial Thoughts

### Potential Approaches

1. **Strengthen existing proof via $(1-x)^n \leq e^{-nx}$ for $x \in [0,1]$**
   - Standard fact: $1 - x \leq e^{-x}$ (from `Real.add_one_le_exp` with $-x$)
   - So $(1 - 1/(d+1))^d \leq e^{-d/(d+1)} \leq e^{-1/2}$ (for $d \geq 1$)
   - Wait, need $(1-1/(d+1))^d \leq 1/e$, which follows from $d/(d+1) \geq 1 - 1/d$
   - Actually $(1-1/n)^n$ increases to $1/e$ from below — need the inequality
   - The key: $(1 - 1/(d+1))^{d+1} \leq 1/e$, so $(1-1/(d+1))^d \leq 1/(e \cdot (1-1/(d+1)))$
   - Why it might work: standard analysis inequalities
   - Risk: direction of inequality subtlety

2. **Direct computation for small d, induction for large d**
   - For d = 1: $(1/2)^1 = 1/2 \leq 1/e \approx 0.368$? NO, $1/2 > 1/e$. 
   - Hmm, the inequality direction: $(1 - 1/(d+1))^d \geq 1/e$ (not ≤)
   - This means $p \leq 1/(e(d+1))$ implies $p \leq (1-1/(d+1))^d / (d+1)$

### Key Difficulties

- Getting the direction of inequalities right for $(1 \pm 1/n)^n$ and $e$
- Understanding exactly where $e$ enters the LLL proof

### What Would a Proof Need?

- `Real.add_one_le_exp` — used to bound $(1-1/(d+1))^d$
- Monotone convergence of $(1-1/n)^n$ to $1/e$
- The connection to the LLL proof's probability argument

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical content is clear but the Lean formalization requires careful handling of real analysis lemmas
- The LLL proof itself needs reorganization to use the sharp criterion
- Comparable effort to `chebyshev-pnt-bridge` type sharpening results

**Estimated Effort**:
- Exploration: 2-4 hours
- Implementation: 1-3 days
- Total: medium, achievable with patience

## References

### Papers
- Erdős, P. and Lovász, L. (1975). "Problems and results on 3-chromatic hypergraphs" — original LLL
- Spencer, J. (1977). "Asymptotic lower bounds for Ramsey functions" — sharp criterion discussion

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Exp` — exponential function
- `Mathlib.Analysis.SpecialFunctions.ExpDeriv` — derivatives of exp

## Metadata

```yaml
tags:
  - combinatorics
  - probabilistic-method
  - LLL
  - euler-number
  - seeker-selected
related_proofs:
  - prob-method-lovasz-local
  - prob-method-expectation
difficulty: medium
source: gallery-gap
created: 2026-04-21
```
