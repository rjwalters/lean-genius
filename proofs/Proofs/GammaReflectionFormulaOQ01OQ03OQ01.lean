/-
# Gamma Reflection OQ-01-OQ-03-OQ-01: The double-factorial half-integer form `Γ(n+1/2) = (2n-1)‼·√π / 2ⁿ`

**Open question (parent `GammaReflectionFormulaOQ01OQ03`).** The parent file proves the
half-integer closed form

> `Γ(n + 1/2) = (2n)! · √π / (4ⁿ · n!)`.

The natural next packaging replaces the central-binomial bookkeeping by the **odd double
factorial** `(2n-1)‼ = 1·3·5·⋯·(2n-1)`, the genuinely "half-integer" object:

> `Γ(n + 1/2) = (2n-1)‼ · √π / 2ⁿ`.

The bridge between the two presentations is the purely combinatorial identity

> `(2n)! / (4ⁿ · n!) = (2n-1)‼ / 2ⁿ`,   equivalently   `(2n)! = (2n-1)‼ · 2ⁿ · n!`,

which is exactly the request of the open question.

## What is new

Mathlib records the two halves of the bridge separately — the *even* double factorial
`Nat.doubleFactorial_two_mul : (2n)‼ = 2ⁿ·n!` and the factorial split
`Nat.factorial_eq_mul_doubleFactorial : (n+1)! = (n+1)‼·n‼` — but it does **not** record
their product `(2n)! = (2n-1)‼·2ⁿ·n!`, nor the resulting odd-double-factorial form of the
half-integer `Γ`. Both are derived here.

## Method

`(2n)! = (2n)‼ · (2n-1)‼` (factorial split at `2n = (2n-1)+1`) and `(2n)‼ = 2ⁿ·n!` give the
integer identity `two_mul_factorial_eq` in a single case split on `n`. Casting to `ℝ` and
clearing `4ⁿ = 2ⁿ·2ⁿ` yields the rational equivalence; substituting it into the parent's
closed form yields the double-factorial `Γ` value.

## References

* Mathlib: `Mathlib/Data/Nat/Factorial/DoubleFactorial.lean`,
  `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`.
* Whittaker & Watson, *A Course of Modern Analysis*, §12.14.
-/
import Mathlib
import Proofs.GammaReflectionFormulaOQ01OQ03

namespace GammaReflectionFormulaOQ01OQ03OQ01

open scoped Real Nat

/-! ## The combinatorial bridge -/

/-- **Factorial in terms of the odd double factorial.**
`(2n)! = (2n-1)‼ · 2ⁿ · n!` for every `n : ℕ`. Combines the factorial split
`(2n)! = (2n)‼·(2n-1)‼` with `(2n)‼ = 2ⁿ·n!`. -/
theorem two_mul_factorial_eq (n : ℕ) :
    (2 * n)! = (2 * n - 1)‼ * 2 ^ n * n ! := by
  cases n with
  | zero => rfl
  | succ k =>
    have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have e2 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [e1, e2, Nat.factorial_eq_mul_doubleFactorial (2 * k + 1),
      show (2 * k + 1) + 1 = 2 * (k + 1) by ring, Nat.doubleFactorial_two_mul (k + 1)]
    ring

/-- **The rational equivalence requested by the open question.**
`(2n)! / (4ⁿ · n!) = (2n-1)‼ / 2ⁿ`. -/
theorem central_eq_oddDoubleFactorial (n : ℕ) :
    ((2 * n).factorial : ℝ) / (4 ^ n * (n.factorial : ℝ))
      = ((2 * n - 1)‼ : ℝ) / 2 ^ n := by
  have hcast : ((2 * n).factorial : ℝ)
      = ((2 * n - 1)‼ : ℝ) * 2 ^ n * (n.factorial : ℝ) := by
    rw [two_mul_factorial_eq]; push_cast; ring
  have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  rw [hcast, h4]
  field_simp

/-! ## The double-factorial half-integer Gamma value -/

/-- **Double-factorial closed form of `Γ` at half-integers.**
`Γ(n + 1/2) = (2n-1)‼ · √π / 2ⁿ` for every `n : ℕ`. Obtained from the parent's central
form `Γ(n+1/2) = (2n)!·√π/(4ⁿ·n!)` by the combinatorial bridge. -/
theorem gamma_nat_add_half_doubleFactorial (n : ℕ) :
    Real.Gamma (n + 1 / 2) = ((2 * n - 1)‼ : ℝ) * Real.sqrt π / 2 ^ n := by
  rw [GammaReflectionFormulaOQ01OQ03.gamma_nat_add_half n]
  have hcast : ((2 * n).factorial : ℝ)
      = ((2 * n - 1)‼ : ℝ) * 2 ^ n * (n.factorial : ℝ) := by
    rw [two_mul_factorial_eq]; push_cast; ring
  have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  rw [hcast, h4]
  field_simp

/-- **Ratio to `Γ(1/2) = √π`.** `Γ(n+1/2)/√π = (2n-1)‼/2ⁿ`: the half-integer Gamma quotient
is the odd double factorial scaled by `2⁻ⁿ`. -/
theorem gamma_nat_add_half_div_sqrt_pi_doubleFactorial (n : ℕ) :
    Real.Gamma (n + 1 / 2) / Real.sqrt π = ((2 * n - 1)‼ : ℝ) / 2 ^ n := by
  rw [gamma_nat_add_half_doubleFactorial]
  have hπ : Real.sqrt π ≠ 0 := by positivity
  field_simp

/-! ## Spot checks -/

/-- `Γ(3/2) = √π/2` read off the double-factorial form at `n = 1` (here `(1)‼ = 1`). -/
theorem gamma_three_half_doubleFactorial : Real.Gamma (3 / 2) = Real.sqrt π / 2 := by
  have h := gamma_nat_add_half_doubleFactorial 1
  norm_num at h
  exact h

/-- `Γ(5/2) = 3√π/4` read off the double-factorial form at `n = 2` (here `(3)‼ = 3`). -/
theorem gamma_five_half_doubleFactorial : Real.Gamma (5 / 2) = 3 * Real.sqrt π / 4 := by
  have h := gamma_nat_add_half_doubleFactorial 2
  norm_num at h
  exact h

end GammaReflectionFormulaOQ01OQ03OQ01
