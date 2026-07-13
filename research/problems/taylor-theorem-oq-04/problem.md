# Problem: Taylor Series Convergence of sin and cos via the Uniform Derivative Bound

**Slug**: taylor-theorem-oq-04
**Created**: 2026-06-30
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: taylor-theorem

## Problem Statement

### Formal Statement

$$
|\sin x - T_n(x)| \le \frac{|x|^{n+1}}{n!} \xrightarrow{n\to\infty} 0,\qquad T_n = \text{taylorWithinEval }\sin\, n\, [0,x]\, 0
$$

### Plain Language

Prove that the Taylor series of sin and cos converges to the function at every real point, using the *bounded-derivatives* mechanism (distinct from the sibling children): because every iterated derivative of sin/cos is uniformly bounded by 1, the Lagrange/uniform remainder bound gives |f(x) - T_n(x)| <= |x|^{n+1}/n! -> 0. This is the classic 'entire function with uniformly bounded derivatives => everywhere-convergent Taylor series' argument.

### Why This Matters

The uniform-derivative-bound technique is a fundamentally different route to convergence than sibling oq-02 (abstract formal power series) or oq-03 (exp via NormedSpace.exp summability). It packages the recognizable alternating-series headline sin x = sum (-1)^k x^{2k+1}/(2k+1)! from a clean remainder estimate.

## Known Results

### What's Already Proven

- Parent entry `taylor-theorem` is verified (0-axiom) in the gallery and supplies the base result this question extends.
- All Mathlib lemmas listed under References below were grep-confirmed to exist in the pinned Mathlib.

### What's Still Open

- The specific target theorems sketched below (currently `sorry`).

### Our Goal

Prove the target sketch below as a self-contained, verified (0-axiom) child of `taylor-theorem`. Category: **extension**.

## Target Lean Sketch

```lean
open Set Filter Topology Nat

theorem sin_taylor_remainder_le (x : ℝ) (hx : 0 < x) (n : ℕ) :
    |Real.sin x - taylorWithinEval Real.sin n (Icc 0 x) 0 x| ≤ x ^ (n + 1) / n ! := by
  have hbound : ∀ y ∈ Icc (0:ℝ) x,
      ‖iteratedDerivWithin (n + 1) Real.sin (Icc 0 x) y‖ ≤ 1 := by
    intro y hy
    rw [Real.iteratedDerivWithin_sin_Icc _ hx hy, Real.norm_eq_abs]
    exact Real.abs_iteratedDeriv_sin_le_one _ y
  have := taylor_mean_remainder_bound (f := Real.sin) (a := 0) (b := x) (C := 1)
    hx.le Real.contDiff_sin.contDiffOn (right_mem_Icc.2 hx.le) hbound
  simpa [Real.norm_eq_abs, abs_of_nonneg hx.le] using this

theorem sin_taylor_remainder_tendsto_zero (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n => Real.sin x - taylorWithinEval Real.sin n (Icc 0 x) 0 x)
      atTop (nhds 0) := by sorry   -- squeeze with x^{n+1}/n! → 0

theorem cos_taylor_remainder_le (x : ℝ) (hx : 0 < x) (n : ℕ) :
    |Real.cos x - taylorWithinEval Real.cos n (Icc 0 x) 0 x| ≤ x ^ (n + 1) / n ! := by sorry
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `taylor-theorem` | Parent: Taylor's theorem with Lagrange remainder | Taylor polynomial, iterated derivatives |
| `taylor-theorem-oq-03` | Sibling: exp convergence via summability (different technique) | NormedSpace.exp |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 6/10  |  **Tractability**: 9/10  |  **Tier**: B

**Justification**: The required Mathlib primitives exist and the proof mirrors the parent's style; the sketch reduces to assembling named lemmas.

### Suggested First Steps

1. Prove `sin_taylor_remainder_le` as sketched (`taylor_mean_remainder_bound` + `iteratedDerivWithin_sin_Icc` + `abs_iteratedDeriv_sin_le_one`).
2. Prove x^{n+1}/n! → 0 from `summable_pow_div_factorial` (factor x·(x^n/n!)), then `squeeze_zero` against the bound for `_tendsto_zero`.
3. Mirror for cos; add the coefficient-pattern corollary sin x = Σ (−1)^k x^{2k+1}/(2k+1)! via `taylor_within_apply` + odd/even iterated-derivative lemmas.

## References

### Mathlib

- `Real.abs_iteratedDeriv_sin_le_one`, `Real.abs_iteratedDeriv_cos_le_one` — Analysis/SpecialFunctions/Trigonometric/Deriv.lean (the uniform bound |fⁿ| ≤ 1)
- `Real.iteratedDerivWithin_sin_Icc`, `..._cos_Icc` — same file (bridge iteratedDerivWithin → iteratedDeriv on Icc)
- `Real.contDiff_sin`, `Real.contDiff_cos` — same file
- `taylor_mean_remainder_bound` — Analysis/Calculus/Taylor.lean (engine: ‖f x − Tₙ‖ ≤ C·(x−a)^{n+1}/n!)
- `taylorWithinEval`, `taylor_within_apply` — Analysis/Calculus/Taylor.lean
- `summable_pow_div_factorial` — Analysis/SpecificLimits/Normed.lean (gives x^{n+1}/n! → 0; squeeze via `squeeze_zero`)

## Metadata

```yaml
tags:
  - calculus
  - analysis
  - taylor-series
  - trigonometric-functions
  - convergence
  - lagrange-remainder
related_proofs:
  - taylor-theorem
  - taylor-theorem-oq-03
difficulty: low
source: proof-suggestion
created: 2026-06-30
```
