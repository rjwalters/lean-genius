/-
# Gamma Reflection OQ-01-OQ-03: The half-integer closed form `Γ(n+1/2) = (2n)!√π / (4ⁿ n!)`

**Open Question (parent `GammaReflectionFormulaOQ01`).** The parent entry establishes
Euler's reflection formula and the special value `Γ(1/2) = √π`. The sibling
`GammaReflectionFormulaOQ01OQ01` evaluated the symmetric Beta value `B(1/2,1/2) = π`.
This file pushes the half-integer thread one structural step further and produces the
**explicit closed form of `Γ` at every half-integer**:

> `Γ(n + 1/2) = (2n)! · √π / (4ⁿ · n!)`   for all `n : ℕ`.

## What is new

Mathlib has the two ingredients in isolation — the special value
`Real.Gamma_one_half_eq : Γ(1/2) = √π` and the functional equation
`Real.Gamma_add_one : Γ(s+1) = s·Γ(s)` — but it does **not** record the resulting
half-integer closed form, nor its packaging through the central binomial coefficient.
Both are derived here by a single induction. The closed form turns every value
`Γ(3/2), Γ(5/2), …` into an elementary expression in factorials and `√π`; the two
spot-check corollaries `Γ(3/2) = √π/2` and `Γ(5/2) = 3√π/4` fall straight out.

## Method

Induction on `n`. The base case `Γ(1/2) = √π` is `Real.Gamma_one_half_eq`. For the step,
write `Γ((n+1)+1/2) = Γ((n+1/2)+1) = (n+1/2)·Γ(n+1/2)` via `Real.Gamma_add_one`, insert
the inductive hypothesis, and clear denominators: the half-integer recursion factor
`n+1/2` is exactly `(2n+2)(2n+1) / (4(n+1))`, which is the ratio of consecutive closed
forms. `field_simp; ring` discharges the resulting factorial identity.

## References

* Mathlib: `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`,
  `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`.
* Whittaker & Watson, *A Course of Modern Analysis*, §12.14 (the duplication formula
  and half-integer values of `Γ`).
-/
import Mathlib

namespace GammaReflectionFormulaOQ01OQ03

open scoped Real

/-! ## The half-integer closed form -/

/-- **Closed form of `Γ` at half-integers.**
`Γ(n + 1/2) = (2n)! · √π / (4ⁿ · n!)` for every `n : ℕ`. Proved by induction from
`Γ(1/2) = √π` (`Real.Gamma_one_half_eq`) and the functional equation
`Γ(s+1) = s·Γ(s)` (`Real.Gamma_add_one`). -/
theorem gamma_nat_add_half (n : ℕ) :
    Real.Gamma (n + 1 / 2) =
      ((2 * n).factorial : ℝ) * Real.sqrt π / (4 ^ n * (n.factorial : ℝ)) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_add, Nat.mul_zero, Nat.factorial_zero, Nat.cast_one,
      pow_zero, one_mul, mul_one, div_one]
    exact Real.Gamma_one_half_eq
  | succ k ih =>
    -- Nonvanishing of the inductive denominators.
    have hk : ((k.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have h4 : (4 : ℝ) ^ k ≠ 0 := by positivity
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hs : ((k : ℝ) + 1 / 2) ≠ 0 := by positivity
    -- Factorial recursions, transported to `ℝ`.
    have hnat : (2 * (k + 1)).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
      have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [h1, Nat.factorial_succ, Nat.factorial_succ]; ring
    have e2 : ((2 * (k + 1)).factorial : ℝ)
        = (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) * ((2 * k).factorial : ℝ) := by
      rw [hnat]; push_cast; ring
    have efk : (((k + 1).factorial) : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    -- Step `Γ((k+1)+1/2) = (k+1/2)·Γ(k+1/2)`, then substitute the closed form.
    have harg : ((k + 1 : ℕ) : ℝ) + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 := by push_cast; ring
    rw [harg, Real.Gamma_add_one hs, ih, e2, efk, pow_succ]
    field_simp
    try ring

/-! ## Consequences -/

/-- **Ratio to `Γ(1/2)`.** Dividing by `√π = Γ(1/2)` exhibits the half-integer Gamma
quotient as a pure rational number, `Γ(n+1/2)/√π = (2n)!/(4ⁿ n!)`. -/
theorem gamma_nat_add_half_div_sqrt_pi (n : ℕ) :
    Real.Gamma (n + 1 / 2) / Real.sqrt π =
      ((2 * n).factorial : ℝ) / (4 ^ n * (n.factorial : ℝ)) := by
  rw [gamma_nat_add_half]
  have hπ : Real.sqrt π ≠ 0 := by positivity
  field_simp
  try ring

/-- **Central-binomial packaging.** Since `(2n)! = C(2n,n)·(n!)²`, the closed form reads
`Γ(n+1/2) = C(2n,n) · n! · √π / 4ⁿ`, tying the half-integer Gamma values to the central
binomial coefficients. -/
theorem gamma_nat_add_half_centralBinom (n : ℕ) :
    Real.Gamma (n + 1 / 2) =
      ((2 * n).choose n : ℝ) * (n.factorial : ℝ) * Real.sqrt π / 4 ^ n := by
  rw [gamma_nat_add_half]
  have hk : ((n.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  -- `C(2n,n)·n!·n! = (2n)!` from `Nat.choose_mul_factorial_mul_factorial`.
  have hchoose : ((2 * n).choose n) * n.factorial * n.factorial = (2 * n).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_mul_of_pos_left n (by norm_num) :
      n ≤ 2 * n)
    rwa [show 2 * n - n = n by omega] at h
  have hcast : ((2 * n).factorial : ℝ)
      = ((2 * n).choose n : ℝ) * (n.factorial : ℝ) * (n.factorial : ℝ) := by
    rw [← hchoose]; push_cast; ring
  rw [hcast]
  field_simp
  try ring

/-! ## Spot checks at small half-integers -/

/-- `Γ(3/2) = √π / 2` (the case `n = 1`). -/
theorem gamma_three_half : Real.Gamma (3 / 2) = Real.sqrt π / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  ring

/-- `Γ(5/2) = 3√π / 4` (the case `n = 2`). -/
theorem gamma_five_half : Real.Gamma (5 / 2) = 3 * Real.sqrt π / 4 := by
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    gamma_three_half]
  ring

end GammaReflectionFormulaOQ01OQ03
