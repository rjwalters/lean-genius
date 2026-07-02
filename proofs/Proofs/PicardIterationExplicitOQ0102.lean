import Mathlib

/-
# Picard iteration as an explicit contraction: successive approximations for `y' = y`

The parent entry (`banach-fixed-point-oq-01-oq-01`, Picard–Lindelöf) obtains the local
solution of an initial value problem as the *abstract* fixed point of the Picard integral
operator

  `(P y)(t) = x₀ + ∫₀ᵗ f(y(s)) ds`

via Banach's contraction principle.  Its second open question asks to **expose the Picard
operator and its contraction constant explicitly**, recovering the solution as the concrete
limit of successive approximations rather than as an opaque fixed point.

This file answers that for the prototypical linear problem

  `y'(t) = y(t)`,   `y(0) = 1`,     so     `f = id`,  `x₀ = 1`,

whose Picard operator is `(P y)(t) = 1 + ∫₀ᵗ y(s) ds`.  Starting from the constant
approximation `y₀ ≡ 1`, the successive approximations are **exactly the Taylor partial
sums of the exponential**:

  `picardIter n t = ∑_{k=0}^{n} tᵏ / k!`.

We prove:

* `picardIter_eq` — the closed form of the `n`‑th approximation (an explicit polynomial),
  so the iteration is fully transparent, not an abstract limit;
* `picardIter_tendsto` — the approximations converge to `exp t` for every `t`, i.e. the
  solution *is* the limit of successive approximations;
* `exp_isFixedPoint` — the limit `exp` is a genuine fixed point of the Picard operator
  `P`, `exp t = 1 + ∫₀ᵗ exp s ds`, and `exp` solves the IVP (`exp_solves`);
* `picard_contraction` — the **explicit contraction estimate**
  `|P y t − P z t| ≤ C · |t|`, so on a time interval `[0, ε]` the operator `P` contracts
  with the explicit constant `ε` (a genuine contraction once `ε < 1`).

Everything is a 0-axiom derivation from Mathlib's interval-integral and exponential API.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace PicardIterationExplicitOQ0102

/-- The Picard integral operator for the IVP `y' = y`, `y(0) = 1`:
`(P y)(t) = 1 + ∫₀ᵗ y(s) ds`. -/
noncomputable def P (y : ℝ → ℝ) (t : ℝ) : ℝ := 1 + ∫ s in (0 : ℝ)..t, y s

/-- The successive Picard approximations, starting from the constant `y₀ ≡ 1`. -/
noncomputable def picardIter : ℕ → ℝ → ℝ
  | 0, _ => 1
  | (n + 1), t => 1 + ∫ s in (0 : ℝ)..t, picardIter n s

/-- The `(n+1)`-term Taylor partial sum of `exp` — the claimed closed form of the
`n`‑th Picard approximation. -/
noncomputable def partialExp (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), t ^ k / (k.factorial : ℝ)

/-- Each Taylor partial sum is continuous (a polynomial). -/
theorem continuous_partialExp (n : ℕ) : Continuous (partialExp n) := by
  unfold partialExp
  exact continuous_finset_sum _ (fun k _ => by fun_prop)

/-- The integral of a single monomial term `sᵏ / k!` over `[0, t]`. -/
theorem integral_term (k : ℕ) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, s ^ k / (k.factorial : ℝ)) =
      t ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  rw [intervalIntegral.integral_div, integral_pow]
  have h0 : (0 : ℝ) ^ (k + 1) = 0 := zero_pow (Nat.succ_ne_zero k)
  rw [h0, sub_zero, Nat.factorial_succ]
  push_cast
  rw [div_div]

/-- **Closed form of the Picard approximations.**  The `n`‑th successive approximation is
exactly the `(n+1)`-term Taylor partial sum of the exponential — the iteration is fully
explicit. -/
theorem picardIter_eq (n : ℕ) : picardIter n = partialExp n := by
  induction n with
  | zero =>
      funext t
      simp [picardIter, partialExp, Nat.factorial]
  | succ n ih =>
      funext t
      show 1 + ∫ s in (0 : ℝ)..t, picardIter n s = partialExp (n + 1) t
      rw [ih]
      simp only [partialExp]
      rw [intervalIntegral.integral_finset_sum]
      · simp only [integral_term]
        rw [Finset.sum_range_succ' (fun k => t ^ k / (k.factorial : ℝ)) (n + 1)]
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
        ring
      · intro k _
        exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- The successive approximations converge to `exp t` for every `t`: the solution is
recovered as the explicit limit of successive approximations. -/
theorem picardIter_tendsto (t : ℝ) :
    Filter.Tendsto (fun n => picardIter n t) Filter.atTop (nhds (Real.exp t)) := by
  have hcf : (fun n => picardIter n t)
      = fun n => ∑ k ∈ Finset.range (n + 1), t ^ k / (k.factorial : ℝ) := by
    funext n; rw [picardIter_eq]; rfl
  rw [hcf]
  have hsum : HasSum (fun n => t ^ n / (n.factorial : ℝ)) (Real.exp t) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ℝ t
  have h := hsum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  simpa [Function.comp] using h

/-- **`exp` is a fixed point of the Picard operator.**  `exp t = 1 + ∫₀ᵗ exp s ds`. -/
theorem exp_isFixedPoint (t : ℝ) : Real.exp t = P Real.exp t := by
  unfold P
  rw [integral_exp, Real.exp_zero]
  ring

/-- The limit `exp` solves the initial value problem `y' = y`, `y(0) = 1`. -/
theorem exp_solves : deriv Real.exp = Real.exp ∧ Real.exp 0 = 1 :=
  ⟨Real.deriv_exp, Real.exp_zero⟩

/-- **Explicit contraction estimate for the Picard operator.**  If `|y s − z s| ≤ C` for
all `s`, then `|P y t − P z t| ≤ C · |t|`.  Hence on the interval `[0, ε]` the operator
`P` is a contraction with the explicit constant `ε` (a genuine contraction once `ε < 1`). -/
theorem picard_contraction {y z : ℝ → ℝ} (hy : Continuous y) (hz : Continuous z)
    {C : ℝ} (hC : ∀ s, |y s - z s| ≤ C) (t : ℝ) :
    |P y t - P z t| ≤ C * |t| := by
  have hsub : P y t - P z t = ∫ s in (0 : ℝ)..t, (y s - z s) := by
    unfold P
    rw [intervalIntegral.integral_sub (hy.intervalIntegrable _ _)
      (hz.intervalIntegrable _ _)]
    ring
  rw [hsub]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t) (C := C) (f := fun s => y s - z s)
    (fun s _ => by simpa [Real.norm_eq_abs] using hC s)
  simpa [Real.norm_eq_abs, sub_zero] using h

/-- The Picard recursion in terms of the operator `P`: `picardIter (n+1) = P (picardIter n)`. -/
theorem picardIter_succ_eq (n : ℕ) : picardIter (n + 1) = P (picardIter n) := rfl

end PicardIterationExplicitOQ0102
