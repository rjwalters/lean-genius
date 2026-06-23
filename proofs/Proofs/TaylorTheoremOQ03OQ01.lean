import Mathlib

/-
# Bridging `taylorWithinEval` to the Exponential Partial Sum

This file answers the open question `taylor-theorem-oq-03-oq-01`: can Mathlib's
local Taylor polynomial `taylorWithinEval Real.exp n (Icc 0 x) 0 x` be identified,
purely from Mathlib lemmas, with the explicit partial sum `∑_{k≤n} xᵏ/k!`?

The answer is yes, and the bridge is short once the right API is located:

- `taylor_within_apply` expands `taylorWithinEval` into a `Finset.sum` whose `k`-th
  summand carries the *local* derivative `iteratedDerivWithin k Real.exp (Icc 0 x) 0`.
- `iteratedDerivWithin_eq_iteratedDeriv` collapses each local derivative to the
  *global* `iteratedDeriv k Real.exp 0`, using that `Real.exp` is `C^∞` and that
  `Icc 0 x` is a `UniqueDiffOn` set containing `0`.
- `iteratedDeriv_exp` evaluates every global derivative of `exp` back to `exp`.

With the bridge in hand we promote the abstract Lagrange remainder
(`taylor_mean_remainder_lagrange_iteratedDeriv`) to a fully explicit statement about
the exponential partial sum: for `x > 0` there is a `ξ ∈ (0, x)` with

  eˣ − ∑_{k≤n} xᵏ/k! = e^ξ · x^{n+1} / (n+1)!.

This makes the Lagrange-remainder conclusion for `exp` self-contained and axiom-free.

## Key Results

- `iteratedDeriv_exp`        : `iteratedDeriv k Real.exp = Real.exp`
- `iteratedDerivWithin_exp_Icc` : local derivatives of `exp` on `Icc 0 x` are `exp`
- `taylorWithinEval_exp_eq_partialSum` : the headline bridge
- `exp_lagrange_remainder_partialSum`  : explicit Lagrange remainder for the partial sum
- `exp_sub_partialSum_le`              : `0 ≤ eˣ − Tₙ(x) ≤ eˣ · x^{n+1}/(n+1)!`

## References

- `Mathlib.Analysis.Calculus.Taylor` — `taylorWithinEval`, `taylor_within_apply`,
  `taylor_mean_remainder_lagrange_iteratedDeriv`
- `Mathlib.Analysis.Calculus.IteratedDeriv.Defs` — `iteratedDerivWithin_eq_iteratedDeriv`
-/

open Set Filter Topology Finset Real
open scoped Nat

set_option linter.unusedSectionVars false

namespace TaylorExpBridge

/-! ## Global derivatives of `exp` -/

/-- The `k`-th iterated derivative of `Real.exp` on `ℝ` is again `Real.exp`. -/
theorem iteratedDeriv_exp (k : ℕ) : iteratedDeriv k Real.exp = Real.exp := by
  induction k with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    ext x
    exact (Real.hasDerivAt_exp x).deriv

/-! ## Local derivatives of `exp` collapse to the global ones -/

/-- On the unique-differentiability set `Icc 0 x` (with `0 < x`), every iterated
derivative-within of `exp` evaluated at the basepoint `0` equals `exp 0 = 1`.

This is the heart of the bridge: it converts the *local* derivatives appearing in
`taylorWithinEval` into the *global* derivatives of the smooth function `exp`. -/
theorem iteratedDerivWithin_exp_Icc (x : ℝ) (hx : 0 < x) (k : ℕ) :
    iteratedDerivWithin k Real.exp (Icc 0 x) 0 = 1 := by
  have hcda : ContDiffAt ℝ k Real.exp 0 := Real.contDiff_exp.contDiffAt.of_le le_top
  have hmem : (0 : ℝ) ∈ Icc (0 : ℝ) x := left_mem_Icc.mpr hx.le
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx) hcda hmem,
    iteratedDeriv_exp, Real.exp_zero]

/-! ## The bridge -/

/-- **Bridge lemma.** For `x > 0`, Mathlib's local Taylor polynomial of `exp` on the
interval `Icc 0 x`, expanded about `0` and evaluated at `x`, is exactly the standard
exponential partial sum:

  `taylorWithinEval Real.exp n (Icc 0 x) 0 x = ∑_{k≤n} xᵏ/k!`. -/
theorem taylorWithinEval_exp_eq_partialSum (x : ℝ) (hx : 0 < x) (n : ℕ) :
    taylorWithinEval Real.exp n (Icc 0 x) 0 x =
      ∑ k ∈ Finset.range (n + 1), x ^ k / (k ! : ℝ) := by
  rw [taylor_within_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [iteratedDerivWithin_exp_Icc x hx k]
  simp only [sub_zero, smul_eq_mul, mul_one]
  ring

/-! ## Explicit Lagrange remainder for the partial sum -/

/-- **Lagrange remainder for the exponential partial sum.**

For `x > 0` and every `n`, there is a point `ξ ∈ (0, x)` such that

  `eˣ − ∑_{k≤n} xᵏ/k! = e^ξ · x^{n+1} / (n+1)!`.

This is the abstract Lagrange remainder, with the local Taylor polynomial replaced by
the explicit partial sum (via `taylorWithinEval_exp_eq_partialSum`) and the local
`(n+1)`-th derivative replaced by `e^ξ` (via `iteratedDeriv_exp`). -/
theorem exp_lagrange_remainder_partialSum (x : ℝ) (hx : 0 < x) (n : ℕ) :
    ∃ ξ ∈ Ioo (0 : ℝ) x,
      Real.exp x - ∑ k ∈ Finset.range (n + 1), x ^ k / (k ! : ℝ) =
        Real.exp ξ * x ^ (n + 1) / (n + 1)! := by
  have hf : ContDiffOn ℝ (n + 1) Real.exp (Icc 0 x) :=
    Real.contDiff_exp.contDiffOn.of_le le_top
  obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx hf
  refine ⟨ξ, hξ, ?_⟩
  rw [taylorWithinEval_exp_eq_partialSum x hx n] at h
  rw [h, iteratedDeriv_exp, sub_zero]

/-- **Two-sided remainder bound.** The exponential partial sum underestimates `eˣ`,
with error controlled by the next Taylor term scaled by `eˣ`:

  `0 ≤ eˣ − ∑_{k≤n} xᵏ/k! ≤ eˣ · x^{n+1}/(n+1)!`.

The upper bound uses `e^ξ ≤ eˣ` for `ξ < x`; the lower bound uses positivity of `e^ξ`. -/
theorem exp_sub_partialSum_le (x : ℝ) (hx : 0 < x) (n : ℕ) :
    0 ≤ Real.exp x - ∑ k ∈ Finset.range (n + 1), x ^ k / (k ! : ℝ) ∧
      Real.exp x - ∑ k ∈ Finset.range (n + 1), x ^ k / (k ! : ℝ) ≤
        Real.exp x * x ^ (n + 1) / (n + 1)! := by
  obtain ⟨ξ, hξ, h⟩ := exp_lagrange_remainder_partialSum x hx n
  rw [Set.mem_Ioo] at hξ
  have hξx : Real.exp ξ ≤ Real.exp x := Real.exp_le_exp.mpr hξ.2.le
  constructor
  · rw [h]; positivity
  · rw [h]; gcongr

/-! ## Sanity checks against the existing partial-sum / convergence machinery -/

/-- The bridge is compatible with summability: `∑ xᵏ/k!` is the convergent exponential
series, so the bridged partial sums converge to `eˣ`. -/
theorem taylorWithinEval_exp_tendsto (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto (fun n => taylorWithinEval Real.exp n (Icc 0 x) 0 x)
      Filter.atTop (nhds (Real.exp x)) := by
  have hsum : HasSum (fun k => x ^ k / (k ! : ℝ)) (Real.exp x) := by
    have h1 : Real.exp x = ∑' k, x ^ k / (k ! : ℝ) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ)]
      exact tsum_congr (fun k => by simp [smul_eq_mul, div_eq_mul_inv, mul_comm])
    rw [h1]
    exact (summable_pow_div_factorial x).hasSum
  have htend := hsum.tendsto_sum_nat
  -- partial sums of length `n+1` still converge to the same limit
  have hshift : Filter.Tendsto
      (fun n => ∑ k ∈ Finset.range (n + 1), x ^ k / (k ! : ℝ))
      Filter.atTop (nhds (Real.exp x)) :=
    htend.comp (Filter.tendsto_add_atTop_nat 1)
  refine hshift.congr (fun n => ?_)
  rw [taylorWithinEval_exp_eq_partialSum x hx n]

/-! ## Verification -/

#check @iteratedDeriv_exp
#check @iteratedDerivWithin_exp_Icc
#check @taylorWithinEval_exp_eq_partialSum
#check @exp_lagrange_remainder_partialSum
#check @exp_sub_partialSum_le
#check @taylorWithinEval_exp_tendsto

end TaylorExpBridge
