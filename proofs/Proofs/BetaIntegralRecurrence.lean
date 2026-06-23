import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic

/-
# The Beta Integral: Recurrence and the Integer Closed Form

## What This Proves

The Euler Beta integral `B(u, v) = ∫₀¹ t^(u-1) (1-t)^(v-1) dt` satisfies the
parameter recurrence

  u · B(u, v+1) = v · B(u+1, v)          (`betaIntegral_recurrence`, Mathlib)

which, together with the Beta–Gamma relation `B(u,v) = Γu·Γv / Γ(u+v)`, pins
down the value of the Beta function on the integer lattice. The centerpiece of
this file is that closed form:

  **`betaIntegral_nat_nat`**:  `B(m+1, n+1) = m! · n! / (m+n+1)!`   for `m, n : ℕ`.

From it we read off concrete values such as `B(1,1) = 1`, `B(2,3) = 1/12`, and
the symmetry `B(m+1,n+1) = B(n+1,m+1)` becomes the manifest symmetry of the
right-hand side under `m ↔ n`.

## Relation to Mathlib

Mathlib (`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`) provides the
recurrence `Complex.betaIntegral_recurrence`, the Beta–Gamma division formula
`Complex.betaIntegral_eq_Gamma_mul_div`, and the *one-sided* evaluation
`Complex.betaIntegral_eval_nat_add_one_right`, which gives
`B(u, n+1) = n! / ∏_{j≤n} (u+j)` for a single integer argument. It does **not**
state the fully symmetric integer closed form `B(m+1,n+1) = m!·n!/(m+n+1)!`,
which is the classical "Beta function of two integers" value. We derive it here
by feeding the two integer arguments through the Beta–Gamma relation and
`Complex.Gamma_nat_eq_factorial`, then specialize to numeric instances.

## Approach

`betaIntegral_nat_nat`: rewrite `B(m+1,n+1)` with `betaIntegral_eq_Gamma_mul_div`
(both real parts are positive), collapse the three Gamma values to factorials
via `Gamma_nat_eq_factorial`, after rewriting the denominator argument
`(m+1)+(n+1)` as `(m+n+1)+1`. The numeric corollaries follow by `push_cast`
and `norm_num`.
-/

namespace BetaIntegralRecurrence

open Complex

/-- **Beta recurrence (the stated identity).** For `Re u > 0`, `Re v > 0`,

  `u · B(u, v+1) = v · B(u+1, v)`.

This is `Complex.betaIntegral_recurrence`; we restate it under our namespace as
the entry's headline identity. -/
theorem beta_recurrence {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    u * betaIntegral u (v + 1) = v * betaIntegral (u + 1) v :=
  betaIntegral_recurrence hu hv

/-- **Integer closed form (new).** For natural numbers `m, n`,

  `B(m+1, n+1) = m! · n! / (m+n+1)!`.

This symmetric two-integer evaluation is not in Mathlib; it is obtained from the
Beta–Gamma relation by collapsing each Gamma value to a factorial. -/
theorem betaIntegral_nat_nat (m n : ℕ) :
    betaIntegral ((m : ℂ) + 1) ((n : ℂ) + 1)
      = (Nat.factorial m : ℂ) * (Nat.factorial n : ℂ)
          / (Nat.factorial (m + n + 1) : ℂ) := by
  have hm : 0 < ((m : ℂ) + 1).re := by
    simp only [add_re, one_re, natCast_re]; positivity
  have hn : 0 < ((n : ℂ) + 1).re := by
    simp only [add_re, one_re, natCast_re]; positivity
  have hsum : ((m : ℂ) + 1) + ((n : ℂ) + 1) = ((m + n + 1 : ℕ) : ℂ) + 1 := by
    push_cast; ring
  rw [betaIntegral_eq_Gamma_mul_div _ _ hm hn, hsum,
      Gamma_nat_eq_factorial m, Gamma_nat_eq_factorial n,
      Gamma_nat_eq_factorial (m + n + 1)]

/-- **Symmetry on the integer lattice.** `B(m+1,n+1) = B(n+1,m+1)`, visibly the
`m ↔ n` symmetry of the closed form. -/
theorem betaIntegral_nat_nat_symm (m n : ℕ) :
    betaIntegral ((m : ℂ) + 1) ((n : ℂ) + 1)
      = betaIntegral ((n : ℂ) + 1) ((m : ℂ) + 1) := by
  rw [betaIntegral_nat_nat, betaIntegral_nat_nat, Nat.add_comm n m]
  ring

/-- `B(1,1) = 1` (the integral of the constant `1` over `[0,1]`). -/
theorem betaIntegral_one_one : betaIntegral 1 1 = 1 := by
  have h := betaIntegral_nat_nat 0 0
  norm_num [Nat.factorial] at h
  linear_combination h

/-- `B(2,3) = 1/12`. -/
theorem betaIntegral_two_three : betaIntegral 2 3 = 1 / 12 := by
  have h := betaIntegral_nat_nat 1 2
  norm_num [Nat.factorial] at h
  linear_combination h

/-- `B(3,3) = 1/30`. -/
theorem betaIntegral_three_three : betaIntegral 3 3 = 1 / 30 := by
  have h := betaIntegral_nat_nat 2 2
  norm_num [Nat.factorial] at h
  linear_combination h

end BetaIntegralRecurrence
