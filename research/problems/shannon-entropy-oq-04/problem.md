# Problem: Shannon Entropy is Maximised by the Uniform Distribution (H ≤ log n)

**Slug**: shannon-entropy-oq-04
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: shannon-entropy

## Problem Statement

### Formal Statement

For a probability vector $p:\{1,\dots,n\}\to[0,1]$ with $\sum_i p_i = 1$ on a support of
size $n\ge 1$,

$$
H(p) \;=\; -\sum_{i} p_i \ln p_i \;\le\; \ln n,
$$

with equality iff $p$ is uniform ($p_i = 1/n$ for all $i$). Equivalently, entropy is a
**concave** function of $p$ and attains its maximum at the barycentre of the simplex.

### Plain Language

The parent entry `shannon-entropy` defines the Shannon entropy of a finite distribution and
establishes its basic properties. This child proves the single most-used inequality about it:
**entropy never exceeds the log of the number of outcomes**, and this bound is achieved
exactly by the uniform distribution. The clean route is Jensen's inequality applied to the
concave function $\ln$: because $x\mapsto \ln x$ is concave, $\sum_i p_i \ln(1/p_i) \le
\ln\!\big(\sum_i p_i\cdot(1/p_i)\big) = \ln n$. The equality case follows from the strict
concavity of $\ln$.

### Why This Matters

`H(p) ≤ log n` is the maximum-entropy principle in its most basic form and the workhorse
bound in coding, statistics, and physics. Mathlib has strict concavity of `log`
(`strictConcaveOn_log_Ioi`) and a Jensen inequality for concave functions
(`ConcaveOn.inner_smul_le_map_sum` / `ConcaveOn.le_map_sum`), but **no** packaged entropy
bound: the target must chain the concavity of `log` through Jensen and then simplify
`∑ pᵢ·(1/pᵢ) = n` on the support. That is a genuine two-lemma assembly, and the equality
case adds the strict part.

## Known Results

### What's Already Proven

- Parent `shannon-entropy` is verified (0-axiom): defines `H(p)` for finite `p`.
- Mathlib: `strictConcaveOn_log_Ioi` (strict concavity of `log` on `(0,∞)`),
  `ConcaveOn.le_map_sum` (finite Jensen for concave functions), `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`
  is *not* needed; `Finset.sum_div`, `Real.log_le_log`, `Real.exp_log`.

### What's Still Open

- The `H(p) ≤ log n` bound and its equality case (currently `sorry`). No named entropy bound
  exists in Mathlib.

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**information theory / inequality completion**.

## Target Lean Sketch

```lean
open Real Finset

/-- Shannon entropy (natural log) of a finite distribution `p` on `Fin n`. -/
noncomputable def H {n : ℕ} (p : Fin n → ℝ) : ℝ := ∑ i, - p i * Real.log (p i)

/-- Maximum-entropy bound: `H(p) ≤ log n` for a probability vector supported on `Fin n`. -/
theorem entropy_le_log_card {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (hpos : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    H p ≤ Real.log n := by
  sorry
  -- Rewrite `H p = ∑ i, p i * log (1 / p i)` (log_inv / neg). Apply Jensen for the concave
  -- `log` with weights `p i` (∑ = 1) to the points `1 / p i`:
  --   ∑ i, p i * log (1/p i) ≤ log (∑ i, p i * (1/p i)) = log (∑ i, 1) = log n.
  -- Uses `ConcaveOn.le_map_sum` with `strictConcaveOn_log_Ioi.concaveOn`, then `mul_one_div`,
  -- `Finset.sum_const`, `Finset.card_fin`.

/-- Equality holds iff `p` is uniform. -/
theorem entropy_eq_log_card_iff {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ)
    (hpos : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    H p = Real.log n ↔ ∀ i, p i = 1 / n := by
  sorry
  -- Forward: strict concavity forces all evaluation points `1/p i` equal, i.e. `p` constant,
  -- then `hsum` pins the constant to `1/n`. Backward: substitute and simplify.
```

Add worked `example`s: `n = 2`, `p = (1/2, 1/2)` gives `H = log 2`; a biased coin
`p = (3/4, 1/4)` gives `H < log 2`; `n = 1` gives `H = 0 = log 1`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `shannon-entropy` | Parent: definition and basic properties | information theory |
| `cauchy-schwarz` | Prototype inequality via convexity | inequalities |
| `basel-problem` | Finite-sum analysis with `log`/series | real analysis |

## Tractability Assessment

**Difficulty**: Medium

**Significance**: 7/10  |  **Tractability**: 7/10  |  **Tier**: B

**Justification**: The bound is a direct Jensen application; the only care needed is aligning
the concave-Jensen API's hypotheses (weights summing to 1, points in `(0,∞)`) and simplifying
`∑ pᵢ·(1/pᵢ) = n`. The equality case leans on the *strict* concavity Mathlib already provides.

### Suggested First Steps

1. Prove the rewrite `H p = ∑ i, p i * log (1 / p i)` via `Real.log_inv`, `neg_mul`.
2. Apply `ConcaveOn.le_map_sum` (from `strictConcaveOn_log_Ioi.concaveOn`) to points `1/p i`.
3. Simplify the RHS argument `∑ i, p i * (1/p i) = ∑ i, 1 = n`; finish the equality case with
   the strict-concavity equality criterion.

## References

### Mathlib

- `Real.strictConcaveOn_log_Ioi` — Analysis/Convex/SpecificFunctions/Basic.lean
- `ConcaveOn.le_map_sum` — Analysis/Convex/Jensen.lean
- `Real.log_inv`, `Real.log_le_log` — Analysis/SpecialFunctions/Log/Basic.lean
- `Finset.sum_const`, `Finset.card_fin` — Algebra/BigOperators/Basic.lean

### Literature

- Cover & Thomas, *Elements of Information Theory*, Thm 2.6.4 (`H(X) ≤ log|𝒳|`, equality iff
  uniform). The maximum-entropy principle is the canonical Jensen application.

## Metadata

```yaml
tags:
  - information-theory
  - shannon-entropy
  - convexity
  - jensen-inequality
related_proofs:
  - shannon-entropy
  - cauchy-schwarz
  - basel-problem
difficulty: medium
source: proof-suggestion
created: 2026-07-01
```
