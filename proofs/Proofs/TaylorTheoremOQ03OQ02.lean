import Mathlib

/-
# A Rigorous Lagrange Remainder Bound for the Taylor Polynomial of `cos`

This file answers the open question `taylor-theorem-oq-03-oq-02`, the second follow-up of
`taylor-theorem-oq-03` ("Taylor Series Convergence of `exp` via the Lagrange Remainder").
Its openQuestion[1] asks whether the parent's Lagrange-remainder method extends from `exp`
to `sin`, `cos`, and other entire functions.

`cos` is the cleanest archetype: whereas the remainder for `exp` carries the growing
factor `eˣ`, every iterated derivative of `cos` is one of `cos, -sin, -cos, sin`, all
bounded in absolute value by `1`. Feeding the *uniform* bound `C = 1` into Mathlib's
`taylor_mean_remainder_bound` yields the clean estimate

  `‖cos x − taylorWithinEval cos n (Icc 0 x) 0 x‖ ≤ x^{n+1} / n!`,    (x ≥ 0)

a remainder that decays for **all** `x` simultaneously, hence convergence of the Taylor
partial sums to `cos`.

## Why this is not already in the gallery

The sibling file `TaylorSinCosConvergence.lean` proves the analogous convergence, but only
after **axiomatizing** the remainder bound itself:

```
axiom cos_taylor_remainder_bound (n : ℕ) (x : ℝ) :
    ‖Real.cos x - cosPartialSum n x‖ ≤ |x| ^ (n + 1) / (Nat.factorial n : ℝ)
```

The present file discharges exactly that bound from Mathlib's `taylor_mean_remainder_bound`
with no new axioms, mirroring the parent's `exp` bridge (`TaylorTheoremOQ03OQ01.lean`). The
`cosPartialSum` of the sibling file is recovered here as the explicit form of
`taylorWithinEval` (`taylorWithinEval_cos_eq_partialSum`).

## Key Results

- `abs_iteratedDeriv_cos_le_one`     : `|iteratedDeriv k cos y| ≤ 1` for every `k, y`
- `cos_lagrange_remainder`           : `‖cos x − taylorWithinEval cos n (Icc 0 x) 0 x‖ ≤ x^{n+1}/n!`
- `taylorWithinEval_cos_eq_partialSum` : `taylorWithinEval` equals the explicit partial sum
- `cos_taylor_remainder_bound_thm`   : the sibling file's axiom, now a theorem (`x ≥ 0`)
- `cos_taylorWithinEval_tendsto`     : the Taylor partial sums of `cos` converge to `cos`

## References

- `Mathlib.Analysis.Calculus.Taylor` — `taylorWithinEval`, `taylor_within_apply`,
  `taylor_mean_remainder_bound`
- `Mathlib.Analysis.Calculus.IteratedDeriv.Defs` — `iteratedDerivWithin_eq_iteratedDeriv`
- Sibling: `TaylorTheoremOQ03OQ01.lean` (the `exp` bridge this mirrors)
-/

open Set Filter Topology Finset Real
open scoped Nat

set_option linter.unusedSectionVars false

namespace TaylorCosBridge

/-! ## Section I: The iterated derivatives of `cos` cycle through `cos, -sin, -cos, sin`

We package the four-fold cycle as a disjunction, proved by a single induction. Each branch
is bounded by `1` in absolute value, giving the uniform derivative bound the Lagrange
estimate needs. -/

/-- `deriv cos = -sin` (as a function equality). -/
theorem deriv_cos_fun : deriv Real.cos = fun x => -Real.sin x := by
  ext x; exact (Real.hasDerivAt_cos x).deriv

/-- `deriv sin = cos` (as a function equality). -/
theorem deriv_sin_fun : deriv Real.sin = Real.cos := by
  ext x; exact (Real.hasDerivAt_sin x).deriv

/-- `deriv (-sin) = -cos`. -/
theorem deriv_neg_sin_fun : deriv (fun x => -Real.sin x) = fun x => -Real.cos x := by
  ext x; exact ((Real.hasDerivAt_sin x).neg).deriv

/-- `deriv (-cos) = sin`. -/
theorem deriv_neg_cos_fun : deriv (fun x => -Real.cos x) = Real.sin := by
  ext x
  have h : HasDerivAt (fun x => -Real.cos x) (Real.sin x) x := by
    simpa using (Real.hasDerivAt_cos x).neg
  exact h.deriv

/-- The `k`-th iterated derivative of `cos` is one of `cos, -sin, -cos, sin`.

Proof by induction on `k`: the four functions rotate under `deriv`
(`cos → -sin → -cos → sin → cos`), so the property is preserved. -/
theorem iteratedDeriv_cos_cycle (k : ℕ) :
    iteratedDeriv k Real.cos = Real.cos ∨
    iteratedDeriv k Real.cos = (fun x => -Real.sin x) ∨
    iteratedDeriv k Real.cos = (fun x => -Real.cos x) ∨
    iteratedDeriv k Real.cos = Real.sin := by
  induction k with
  | zero => left; rw [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    rcases ih with h | h | h | h
    · -- cos → -sin
      right; left; rw [h, deriv_cos_fun]
    · -- -sin → -cos
      right; right; left; rw [h, deriv_neg_sin_fun]
    · -- -cos → sin
      right; right; right; rw [h, deriv_neg_cos_fun]
    · -- sin → cos
      left; rw [h, deriv_sin_fun]

/-- **Uniform derivative bound.** Every iterated derivative of `cos` is bounded by `1` in
absolute value, since each is one of `±cos, ±sin`. -/
theorem abs_iteratedDeriv_cos_le_one (k : ℕ) (y : ℝ) :
    |iteratedDeriv k Real.cos y| ≤ 1 := by
  rcases iteratedDeriv_cos_cycle k with h | h | h | h <;>
    rw [show iteratedDeriv k Real.cos y = _ from congrFun h y]
  · exact Real.abs_cos_le_one y
  · rw [abs_neg]; exact Real.abs_sin_le_one y
  · rw [abs_neg]; exact Real.abs_cos_le_one y
  · exact Real.abs_sin_le_one y

/-! ## Section II: Local derivatives on `Icc 0 x` collapse to the global bound -/

/-- On `Icc 0 x` (with `0 < x`), the derivative-within of `cos` agrees with the global
iterated derivative, hence inherits the uniform bound `1`. -/
theorem norm_iteratedDerivWithin_cos_Icc_le (x : ℝ) (hx : 0 < x) (k : ℕ)
    (y : ℝ) (hy : y ∈ Icc (0 : ℝ) x) :
    ‖iteratedDerivWithin k Real.cos (Icc 0 x) y‖ ≤ 1 := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
    (Real.contDiff_cos.contDiffAt.of_le le_top) hy]
  simpa [Real.norm_eq_abs] using abs_iteratedDeriv_cos_le_one k y

/-! ## Section III: The Lagrange remainder bound for `cos` -/

/-- **Lagrange remainder bound for `cos` (`x > 0`).** Plugging the uniform derivative bound
`C = 1` into `taylor_mean_remainder_bound` gives

  `‖cos x − taylorWithinEval cos n (Icc 0 x) 0 x‖ ≤ x^{n+1}/n!`. -/
theorem cos_lagrange_remainder_pos (x : ℝ) (hx : 0 < x) (n : ℕ) :
    ‖Real.cos x - taylorWithinEval Real.cos n (Icc 0 x) 0 x‖ ≤ x ^ (n + 1) / n ! := by
  have hf : ContDiffOn ℝ (n + 1) Real.cos (Icc 0 x) :=
    Real.contDiff_cos.contDiffOn.of_le le_top
  have hmem : x ∈ Icc (0 : ℝ) x := right_mem_Icc.mpr hx.le
  have hC : ∀ y ∈ Icc (0 : ℝ) x, ‖iteratedDerivWithin (n + 1) Real.cos (Icc 0 x) y‖ ≤ 1 :=
    fun y hy => norm_iteratedDerivWithin_cos_Icc_le x hx (n + 1) y hy
  have h := taylor_mean_remainder_bound hx.le hf hmem hC
  simpa [sub_zero, one_mul] using h

/-- **Lagrange remainder bound for `cos` (`x ≥ 0`).** The same estimate, with the `x = 0`
endpoint included (where both sides vanish). -/
theorem cos_lagrange_remainder (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    ‖Real.cos x - taylorWithinEval Real.cos n (Icc 0 x) 0 x‖ ≤ x ^ (n + 1) / n ! := by
  rcases hx.lt_or_eq with hlt | heq
  · exact cos_lagrange_remainder_pos x hlt n
  · subst heq; simp

/-! ## Section IV: The explicit partial sum

We identify Mathlib's local Taylor polynomial with the standard partial sum
`∑_{k≤n} (iteratedDeriv k cos 0) · xᵏ/k!`, recovering the sibling file's `cosPartialSum`. -/

/-- **Bridge.** For `x > 0`, `taylorWithinEval cos n (Icc 0 x) 0 x` equals the explicit
partial sum `∑_{k≤n} (iteratedDeriv k cos 0) · xᵏ/k!`. -/
theorem taylorWithinEval_cos_eq_partialSum (x : ℝ) (hx : 0 < x) (n : ℕ) :
    taylorWithinEval Real.cos n (Icc 0 x) 0 x =
      ∑ k ∈ Finset.range (n + 1), (iteratedDeriv k Real.cos 0) * x ^ k / (k ! : ℝ) := by
  rw [taylor_within_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hmem : (0 : ℝ) ∈ Icc (0 : ℝ) x := left_mem_Icc.mpr hx.le
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
    (Real.contDiff_cos.contDiffAt.of_le le_top) hmem]
  rw [sub_zero, smul_eq_mul]
  ring

/-- The explicit cos partial sum (matching `cosPartialSum` of `TaylorSinCosConvergence`). -/
noncomputable def cosPartialSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (iteratedDeriv k Real.cos 0) * x ^ k / (k ! : ℝ)

/-- **The sibling file's axiom, discharged as a theorem (`x ≥ 0`).**

`TaylorSinCosConvergence.lean` postulates
`‖cos x − cosPartialSum n x‖ ≤ |x|^{n+1}/n!` as an axiom. Here it is proved from
`taylor_mean_remainder_bound` for `x ≥ 0`. -/
theorem cos_taylor_remainder_bound_thm (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ‖Real.cos x - cosPartialSum n x‖ ≤ |x| ^ (n + 1) / (n ! : ℝ) := by
  rcases hx.lt_or_eq with hlt | heq
  · rw [cosPartialSum, ← taylorWithinEval_cos_eq_partialSum x hlt n, abs_of_pos hlt]
    exact cos_lagrange_remainder_pos x hlt n
  · subst heq
    simp [cosPartialSum, Finset.sum_range_succ']

/-! ## Section V: Convergence of the Taylor partial sums to `cos` -/

/-- `x^{n+1}/n! → 0`, the decay driving convergence. -/
theorem pow_succ_div_factorial_tendsto (x : ℝ) :
    Tendsto (fun n => x ^ (n + 1) / (n ! : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun n => |x| ^ n / (n ! : ℝ)) atTop (𝓝 0) :=
    (summable_pow_div_factorial |x|).tendsto_atTop_zero
  have h2 : Tendsto (fun n => |x| * (|x| ^ n / (n ! : ℝ))) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = |x| * 0 from by ring]; exact h.const_mul _
  refine squeeze_zero_norm' ?_ h2
  filter_upwards with n
  rw [Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast, pow_succ]
  apply le_of_eq; ring

/-- **Convergence (`x ≥ 0`).** The local Taylor polynomials of `cos` converge to `cos x`,
derived from the Lagrange remainder bound via squeezing. -/
theorem cos_taylorWithinEval_tendsto (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n => taylorWithinEval Real.cos n (Icc 0 x) 0 x) atTop (𝓝 (Real.cos x)) := by
  have hrem : Tendsto (fun n => Real.cos x - taylorWithinEval Real.cos n (Icc 0 x) 0 x)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (pow_succ_div_factorial_tendsto x)
    filter_upwards with n
    exact cos_lagrange_remainder_pos x hx n
  have := hrem.const_sub (Real.cos x)
  simpa [sub_sub_cancel] using this

/-- **Convergence via the explicit partial sum.** `cosPartialSum n x → cos x` for `x ≥ 0`,
the axiom-free counterpart of `TaylorSinCosConvergence.cosPartialSum_tendsto`. -/
theorem cosPartialSum_tendsto (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n => cosPartialSum n x) atTop (𝓝 (Real.cos x)) := by
  refine (cos_taylorWithinEval_tendsto x hx).congr (fun n => ?_)
  rw [cosPartialSum, ← taylorWithinEval_cos_eq_partialSum x hx n]

/-! ## Verification -/

#check @abs_iteratedDeriv_cos_le_one
#check @cos_lagrange_remainder
#check @taylorWithinEval_cos_eq_partialSum
#check @cos_taylor_remainder_bound_thm
#check @cos_taylorWithinEval_tendsto
#check @cosPartialSum_tendsto

end TaylorCosBridge
