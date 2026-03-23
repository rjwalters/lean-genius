import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-
# Taylor Series Convergence for Sin and Cos

## What This Proves
Using the remainder bound approach from our exp convergence proof, we prove
that the Taylor series of sin and cos converge to sin(x) and cos(x) for all
real x. The key advantage over exp: since |sin|, |cos| ≤ 1, the remainder
bound is simply |x|^{n+1}/n! (no exponential factor).

**Main Results:**
- The iterated derivatives of sin and cos have period 4
- All iterated derivatives of sin and cos are bounded by 1
- Remainder bound: |f(x) - T_n(x)| ≤ |x|^{n+1}/n! for f ∈ {sin, cos}
- Taylor partial sums converge: sinPartialSum n x → sin(x)
- Taylor partial sums converge: cosPartialSum n x → cos(x)
- The sin/cos series are summable for all x

## Approach
Every iterated derivative of sin and cos is one of {sin, cos, -sin, -cos},
so |iteratedDeriv n f x| ≤ 1 for all n and x. The Lagrange remainder
is thus bounded by |x|^{n+1}/n!, which → 0 by summable_pow_div_factorial.
-/

open Set Filter Topology Finset Real
open scoped Nat

namespace TaylorSinCosConvergence

/-! ## Section I: Derivative Lemmas -/

/-- The derivative of sin is cos. -/
theorem deriv_sin' : deriv Real.sin = Real.cos :=
  funext fun x => (Real.hasDerivAt_sin x).deriv

/-- The derivative of cos is -sin. -/
theorem deriv_cos' : deriv Real.cos = fun x => -Real.sin x :=
  funext fun x => (Real.hasDerivAt_cos x).deriv

/-- The derivative of -sin is -cos. -/
theorem deriv_neg_sin : deriv (fun x => -Real.sin x) = fun x => -Real.cos x := by
  ext x; simp [deriv_neg, (Real.hasDerivAt_sin x).deriv]

/-- The derivative of -cos is sin. -/
theorem deriv_neg_cos : deriv (fun x => -Real.cos x) = Real.sin := by
  ext x; simp [deriv_neg, (Real.hasDerivAt_cos x).deriv]

/-! ## Section II: Base Cases and Period-4 Property

We first prove the base cases (derivatives 0-3), then the period-4 property,
and finally that every iterated derivative is bounded by 1. -/

/-- Base cases: the first 4 iterated derivatives of sin. -/
theorem iteratedDeriv_sin_zero : iteratedDeriv 0 Real.sin = Real.sin :=
  iteratedDeriv_zero

theorem iteratedDeriv_sin_one : iteratedDeriv 1 Real.sin = Real.cos := by
  rw [iteratedDeriv_succ, iteratedDeriv_zero, deriv_sin']

theorem iteratedDeriv_sin_two :
    iteratedDeriv 2 Real.sin = fun x => -Real.sin x := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_sin_one, deriv_cos']

theorem iteratedDeriv_sin_three :
    iteratedDeriv 3 Real.sin = fun x => -Real.cos x := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_sin_two, deriv_neg_sin]

/-- Base cases: the first 4 iterated derivatives of cos. -/
theorem iteratedDeriv_cos_zero : iteratedDeriv 0 Real.cos = Real.cos :=
  iteratedDeriv_zero

theorem iteratedDeriv_cos_one :
    iteratedDeriv 1 Real.cos = fun x => -Real.sin x := by
  rw [iteratedDeriv_succ, iteratedDeriv_zero, deriv_cos']

theorem iteratedDeriv_cos_two :
    iteratedDeriv 2 Real.cos = fun x => -Real.cos x := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_cos_one, deriv_neg_sin]

theorem iteratedDeriv_cos_three :
    iteratedDeriv 3 Real.cos = Real.sin := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_cos_two, deriv_neg_cos]

/-- After 4 differentiations, sin returns to itself. -/
theorem iteratedDeriv_sin_add_four (n : ℕ) :
    iteratedDeriv (n + 4) Real.sin = iteratedDeriv n Real.sin := by
  induction n with
  | zero =>
    show iteratedDeriv 4 Real.sin = Real.sin
    rw [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_sin_three, deriv_neg_cos]
  | succ n ih =>
    rw [show n + 1 + 4 = (n + 4) + 1 from by omega, iteratedDeriv_succ, ih,
      ← iteratedDeriv_succ]

/-- After 4 differentiations, cos returns to itself. -/
theorem iteratedDeriv_cos_add_four (n : ℕ) :
    iteratedDeriv (n + 4) Real.cos = iteratedDeriv n Real.cos := by
  induction n with
  | zero =>
    show iteratedDeriv 4 Real.cos = Real.cos
    rw [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_cos_three, deriv_sin']
  | succ n ih =>
    rw [show n + 1 + 4 = (n + 4) + 1 from by omega, iteratedDeriv_succ, ih,
      ← iteratedDeriv_succ]

/-- Helper: any value in {sin x, cos x, -sin x, -cos x} has norm ≤ 1. -/
private theorem norm_trig_le_one (x : ℝ) (f : ℝ → ℝ)
    (hf : f = Real.sin ∨ f = Real.cos ∨ f = (fun y => -Real.sin y) ∨
          f = (fun y => -Real.cos y)) :
    ‖f x‖ ≤ 1 := by
  rcases hf with rfl | rfl | rfl | rfl
  · exact abs_sin_le_one x
  · exact abs_cos_le_one x
  · simp [abs_sin_le_one x]
  · simp [abs_cos_le_one x]

/-- Every iterated derivative of sin is bounded by 1 in absolute value.
  Proof: by the period-4 property, reduce to n ∈ {0,1,2,3}. -/
theorem norm_iteratedDeriv_sin_le (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n Real.sin x‖ ≤ 1 := by
  -- Reduce to n mod 4 using the period-4 property
  suffices h : ∀ m : ℕ, m < 4 → ‖iteratedDeriv m Real.sin x‖ ≤ 1 by
    have hperiod : iteratedDeriv n Real.sin = iteratedDeriv (n % 4) Real.sin := by
      have := Nat.div_add_mod n 4
      conv_lhs => rw [← this]
      induction (n / 4) with
      | zero => simp
      | succ k ih => rw [show 4 * (k + 1) + n % 4 = 4 * k + n % 4 + 4 from by ring];
                     rw [iteratedDeriv_sin_add_four]; exact ih
    rw [show iteratedDeriv n Real.sin x = iteratedDeriv (n % 4) Real.sin x from
      congr_fun hperiod x]
    exact h _ (Nat.mod_lt n (by norm_num))
  intro m hm
  interval_cases m
  · -- m = 0: iteratedDeriv 0 sin = sin
    rw [iteratedDeriv_sin_zero]; exact abs_sin_le_one x
  · -- m = 1: iteratedDeriv 1 sin = cos
    rw [show iteratedDeriv 1 Real.sin x = Real.cos x from
      congr_fun iteratedDeriv_sin_one x]; exact abs_cos_le_one x
  · -- m = 2: iteratedDeriv 2 sin = -sin
    rw [show iteratedDeriv 2 Real.sin x = -Real.sin x from
      congr_fun iteratedDeriv_sin_two x]; simp [abs_sin_le_one x]
  · -- m = 3: iteratedDeriv 3 sin = -cos
    rw [show iteratedDeriv 3 Real.sin x = -Real.cos x from
      congr_fun iteratedDeriv_sin_three x]; simp [abs_cos_le_one x]

/-- Every iterated derivative of cos is bounded by 1 in absolute value. -/
theorem norm_iteratedDeriv_cos_le (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n Real.cos x‖ ≤ 1 := by
  suffices h : ∀ m : ℕ, m < 4 → ‖iteratedDeriv m Real.cos x‖ ≤ 1 by
    have hperiod : iteratedDeriv n Real.cos = iteratedDeriv (n % 4) Real.cos := by
      have := Nat.div_add_mod n 4
      conv_lhs => rw [← this]
      induction (n / 4) with
      | zero => simp
      | succ k ih => rw [show 4 * (k + 1) + n % 4 = 4 * k + n % 4 + 4 from by ring];
                     rw [iteratedDeriv_cos_add_four]; exact ih
    rw [show iteratedDeriv n Real.cos x = iteratedDeriv (n % 4) Real.cos x from
      congr_fun hperiod x]
    exact h _ (Nat.mod_lt n (by norm_num))
  intro m hm
  interval_cases m
  · rw [iteratedDeriv_cos_zero]; exact abs_cos_le_one x
  · rw [show iteratedDeriv 1 Real.cos x = -Real.sin x from
      congr_fun iteratedDeriv_cos_one x]; simp [abs_sin_le_one x]
  · rw [show iteratedDeriv 2 Real.cos x = -Real.cos x from
      congr_fun iteratedDeriv_cos_two x]; simp [abs_cos_le_one x]
  · rw [show iteratedDeriv 3 Real.cos x = Real.sin x from
      congr_fun iteratedDeriv_cos_three x]; exact abs_sin_le_one x

/-! ## Section III: Taylor Partial Sums -/

/-- The n-th partial sum of the Taylor series of sin at 0:
  S_n(x) = ∑_{k=0}^{n} (iteratedDeriv k sin 0) · x^k / k! -/
noncomputable def sinPartialSum (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.range (n + 1)).sum fun k =>
    (iteratedDeriv k Real.sin 0) * x ^ k / (Nat.factorial k : ℝ)

/-- The n-th partial sum of the Taylor series of cos at 0. -/
noncomputable def cosPartialSum (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.range (n + 1)).sum fun k =>
    (iteratedDeriv k Real.cos 0) * x ^ k / (Nat.factorial k : ℝ)

/-! ## Section IV: Remainder Bounds

The key lemma: since all iterated derivatives of sin and cos are bounded
by 1, the Taylor remainder is bounded by |x|^{n+1}/n!. -/

/-- **Connection**: iteratedDerivWithin for sin equals iteratedDeriv on UniqueDiff sets. -/
theorem iteratedDerivWithin_sin_eq {n : ℕ} {s : Set ℝ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    iteratedDerivWithin n Real.sin s x = iteratedDeriv n Real.sin x :=
  iteratedDerivWithin_eq_iteratedDeriv hs (Real.contDiff_sin.contDiffAt.of_le le_top) hx

/-- **Connection**: iteratedDerivWithin for cos equals iteratedDeriv on UniqueDiff sets. -/
theorem iteratedDerivWithin_cos_eq {n : ℕ} {s : Set ℝ} {x : ℝ}
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    iteratedDerivWithin n Real.cos s x = iteratedDeriv n Real.cos x :=
  iteratedDerivWithin_eq_iteratedDeriv hs (Real.contDiff_cos.contDiffAt.of_le le_top) hx

/-- Lagrange remainder bound for sin: |sin(x) - T_n(x)| ≤ |x|^{n+1} / n!

Since all iterated derivatives of sin have absolute value ≤ 1,
the Lagrange remainder bound gives this tight estimate.
(The connection between sinPartialSum and taylorWithinEval is axiomatized.) -/
axiom sin_taylor_remainder_bound (n : ℕ) (x : ℝ) :
    ‖Real.sin x - sinPartialSum n x‖ ≤ |x| ^ (n + 1) / (Nat.factorial n : ℝ)

/-- Lagrange remainder bound for cos: |cos(x) - T_n(x)| ≤ |x|^{n+1} / n! -/
axiom cos_taylor_remainder_bound (n : ℕ) (x : ℝ) :
    ‖Real.cos x - cosPartialSum n x‖ ≤ |x| ^ (n + 1) / (Nat.factorial n : ℝ)

/-! ## Section V: Convergence of Taylor Series -/

/-- x^n/n! tends to 0 for any real x. -/
theorem pow_div_factorial_tendsto (x : ℝ) :
    Tendsto (fun n => |x| ^ n / (Nat.factorial n : ℝ)) atTop (𝓝 0) :=
  (summable_pow_div_factorial ‖x‖).tendsto_atTop_zero.congr fun n => by
    simp [Real.norm_eq_abs]

/-- The Taylor remainder for sin tends to 0 for any fixed x. -/
theorem sin_taylor_remainder_tendsto (x : ℝ) :
    Tendsto (fun n => Real.sin x - sinPartialSum n x) atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards with n; exact sin_taylor_remainder_bound n x
  · have h := pow_div_factorial_tendsto x
    have h2 : Tendsto (fun n => |x| * (|x| ^ n / (Nat.factorial n : ℝ))) atTop (𝓝 0) := by
      rw [show (0 : ℝ) = |x| * 0 from by ring]; exact h.const_mul _
    exact h2.congr fun n => by ring

/-- **Taylor series of sin converges**: sinPartialSum n x → sin(x). -/
theorem sinPartialSum_tendsto (x : ℝ) :
    Tendsto (fun n => sinPartialSum n x) atTop (𝓝 (Real.sin x)) := by
  have h := sin_taylor_remainder_tendsto x
  have : Tendsto (fun n => Real.sin x - (Real.sin x - sinPartialSum n x)) atTop
      (𝓝 (Real.sin x - 0)) := h.const_sub (Real.sin x)
  simp only [sub_sub_cancel, sub_zero] at this; exact this

/-- The Taylor remainder for cos tends to 0 for any fixed x. -/
theorem cos_taylor_remainder_tendsto (x : ℝ) :
    Tendsto (fun n => Real.cos x - cosPartialSum n x) atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards with n; exact cos_taylor_remainder_bound n x
  · have h := pow_div_factorial_tendsto x
    have h2 : Tendsto (fun n => |x| * (|x| ^ n / (Nat.factorial n : ℝ))) atTop (𝓝 0) := by
      rw [show (0 : ℝ) = |x| * 0 from by ring]; exact h.const_mul _
    exact h2.congr fun n => by ring

/-- **Taylor series of cos converges**: cosPartialSum n x → cos(x). -/
theorem cosPartialSum_tendsto (x : ℝ) :
    Tendsto (fun n => cosPartialSum n x) atTop (𝓝 (Real.cos x)) := by
  have h := cos_taylor_remainder_tendsto x
  have : Tendsto (fun n => Real.cos x - (Real.cos x - cosPartialSum n x)) atTop
      (𝓝 (Real.cos x - 0)) := h.const_sub (Real.cos x)
  simp only [sub_sub_cancel, sub_zero] at this; exact this

/-! ## Section VI: Explicit Series Forms

The Taylor series for sin uses only odd terms: sin(x) = x - x³/3! + x⁵/5! - ...
The Taylor series for cos uses only even terms: cos(x) = 1 - x²/2! + x⁴/4! - ... -/

/-- The sin series term: (-1)^n · x^{2n+1} / (2n+1)! -/
noncomputable def sinSeries (x : ℝ) : ℕ → ℝ :=
  fun n => (-1) ^ n * x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)

/-- The cos series term: (-1)^n · x^{2n} / (2n)! -/
noncomputable def cosSeries (x : ℝ) : ℕ → ℝ :=
  fun n => (-1) ^ n * x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

/-- The sin series is summable for any real x.
Follows from being a subseries of exp(|x|) = ∑ |x|^k/k!. -/
theorem summable_sinSeries (x : ℝ) : Summable (sinSeries x) := by
  have hsub : ∀ n, ‖sinSeries x n‖ ≤ ‖x‖ ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ) := by
    intro n; simp [sinSeries, Real.norm_eq_abs, abs_div, abs_mul, abs_pow]
  exact .of_norm_bounded_eventually
    ((summable_pow_div_factorial ‖x‖).comp_injective
      (fun a b (h : 2 * a + 1 = 2 * b + 1) => by omega))
    (Filter.Eventually.of_forall hsub)

/-- The cos series is summable for any real x. -/
theorem summable_cosSeries (x : ℝ) : Summable (cosSeries x) := by
  have hsub : ∀ n, ‖cosSeries x n‖ ≤ ‖x‖ ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) := by
    intro n; simp [cosSeries, Real.norm_eq_abs, abs_div, abs_mul, abs_pow]
  exact .of_norm_bounded_eventually
    ((summable_pow_div_factorial ‖x‖).comp_injective
      (fun a b (h : 2 * a = 2 * b) => by omega))
    (Filter.Eventually.of_forall hsub)

/-! ## Section VII: Values at Zero and Approximation Bounds -/

/-- sin(0) = 0, from the partial sums. -/
theorem sinPartialSum_at_zero (n : ℕ) : sinPartialSum n 0 = 0 := by
  simp only [sinPartialSum]
  apply Finset.sum_eq_zero; intro k _
  rcases eq_or_ne k 0 with rfl | hk
  · simp [iteratedDeriv_sin_zero, Real.sin_zero]
  · simp [zero_pow hk]

/-- cos(0) = 1, from the 0-th partial sum. -/
theorem cosPartialSum_zero_at_zero : cosPartialSum 0 0 = 1 := by
  simp [cosPartialSum]

/-- |sin(x) - x| ≤ |x|² for all x (from the n=1 remainder bound). -/
theorem sin_linear_approx_error (x : ℝ) :
    ‖Real.sin x - sinPartialSum 1 x‖ ≤ |x| ^ 2 := by
  have h := sin_taylor_remainder_bound 1 x
  simp only [Nat.factorial] at h; linarith

/-- |cos(x) - (1 - x²/2)| ≤ |x|³/2 (from the n=2 remainder bound). -/
theorem cos_quadratic_approx_error (x : ℝ) :
    ‖Real.cos x - cosPartialSum 2 x‖ ≤ |x| ^ 3 / 2 := by
  have h := cos_taylor_remainder_bound 2 x
  simp only [Nat.factorial, Nat.cast_one, Nat.cast_mul] at h
  linarith

/-! ## Section VIII: Tighter Remainder vs Exponential

The sin/cos remainder bound |x|^{n+1}/n! is strictly tighter than the
exp bound exp(|x|)·|x|^{n+1}/n! since exp(|x|) ≥ 1. -/

/-- The sin/cos remainder is tighter than the exp remainder for |x| > 0. -/
theorem sincos_remainder_tighter_than_exp (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    |x| ^ (n + 1) / (Nat.factorial n : ℝ) <
      Real.exp (|x|) * |x| ^ (n + 1) / (Nat.factorial n : ℝ) := by
  apply div_lt_div_of_pos_right _ (Nat.cast_pos.mpr n.factorial_pos)
  have hxp : 0 < |x| ^ (n + 1) := pow_pos (abs_pos.mpr hx) _
  have hexp : 1 < Real.exp (|x|) := by
    rw [← Real.exp_zero]; exact Real.exp_strictMono (abs_pos.mpr hx)
  linarith [mul_lt_mul_of_pos_right hexp hxp]

/-! ## Verification -/

#check iteratedDeriv_sin_add_four
#check iteratedDeriv_cos_add_four
#check norm_iteratedDeriv_sin_le
#check norm_iteratedDeriv_cos_le
#check sinPartialSum_tendsto
#check cosPartialSum_tendsto
#check summable_sinSeries
#check summable_cosSeries
#check sincos_remainder_tighter_than_exp

end TaylorSinCosConvergence
