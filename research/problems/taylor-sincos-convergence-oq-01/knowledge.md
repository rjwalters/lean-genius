# Knowledge: taylor-sincos-convergence-oq-01

**Problem**: Eliminate remainder axioms by bridging sinPartialSum to Mathlib sin
**Selected**: 2026-04-05
**Status**: EMPTY → SEEKER INITIALIZED

---

## Problem Statement

In `proofs/Proofs/TaylorSinCosConvergence.lean`, two `axiom` declarations block full verification:

```lean
axiom sin_taylor_remainder_bound (n : ℕ) (x : ℝ) :
    ‖Real.sin x - sinPartialSum n x‖ ≤ |x| ^ (n + 1) / (Nat.factorial n : ℝ)

axiom cos_taylor_remainder_bound (n : ℕ) (x : ℝ) :
    ‖Real.cos x - cosPartialSum n x‖ ≤ |x| ^ (n + 1) / (Nat.factorial n : ℝ)
```

Goal: convert these `axiom` declarations to `theorem ... := by sorry` (or full proofs) by connecting `sinPartialSum`/`cosPartialSum` to Mathlib's `taylorWithinEval`.

---

## Key Definitions

**Custom (in proof file)**:
```lean
noncomputable def sinPartialSum (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.range (n + 1)).sum fun k =>
    (iteratedDeriv k Real.sin 0) * x ^ k / (Nat.factorial k : ℝ)
```

**Mathlib's Taylor polynomial** (from `Mathlib.Analysis.Calculus.Taylor`):
- `taylorWithinEval f n s a x` — uses `iteratedDerivWithin n f s a`

**Bridge already proved**:
```lean
theorem iteratedDerivWithin_sin_eq {n : ℕ} {s : Set ℝ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    iteratedDerivWithin n Real.sin s x = iteratedDeriv n Real.sin x
```

---

## Technical Gap

`sinPartialSum` uses `iteratedDeriv` (global derivatives), while Mathlib's Taylor theorem (`taylor_mean_remainder_bound`) works with `taylorWithinEval` which uses `iteratedDerivWithin`.

The bridge lemma `iteratedDerivWithin_sin_eq` shows they agree on `UniqueDiffOn` sets. The approach is:
1. Show `sinPartialSum n x = taylorWithinEval ℝ n Real.sin s 0 x` for some `s` containing 0 and x (e.g., `Set.univ` or `Set.Icc (-R) R`)
2. Apply Mathlib's `taylor_mean_remainder_bound` with the universal bound `‖iteratedDeriv k sin t‖ ≤ 1`

---

## Mathlib API to Use

- `taylorWithinEval`: The n-th Taylor polynomial of f at a, evaluated at x
- `taylor_mean_remainder_bound`: Gives `‖f x - taylorWithinEval f n s a x‖ ≤ ...`
  - Requires: `ContDiffOn`, `ContinuousOn` of n-th derivative on interval
- `uniqueDiffOn_univ` or `uniqueDiffOn_Ioo`: For UniqueDiff sets
- `Real.contDiff_sin`, `Real.contDiff_cos`: sin/cos are C∞

## Approach

**Step 1**: Prove `sinPartialSum_eq_taylorWithinEval`:
```lean
theorem sinPartialSum_eq_taylorWithinEval (n : ℕ) (x : ℝ) :
    sinPartialSum n x = taylorWithinEval ℝ n Set.univ Real.sin 0 x
```
This requires unfolding `taylorWithinEval` definition and showing term-by-term equality using `iteratedDerivWithin_sin_eq`.

**Step 2**: Apply Taylor remainder bound from Mathlib with C=1:
```lean
-- Use taylor_mean_remainder_bound or taylor_mean_remainder_lagrange
-- with the bound ‖iteratedDeriv (n+1) Real.sin t‖ ≤ 1
```

---

## Key Facts Known

- `sinPartialSum` cycles through {sin,cos,-sin,-cos} values at 0
- All iterated derivatives of sin/cos are bounded by 1 (proved in file)
- `iteratedDerivWithin_sin_eq` proves the bridge on UniqueDiff sets
- The remaining structure (convergence proofs, summability) is fully proved

---

## Gallery Status

- `src/data/proofs/taylor-sincos-convergence/meta.json`: axiomCount = 2, status = axiomatized
- Resolving this OQ would move status to `verified` with axiomCount = 0
