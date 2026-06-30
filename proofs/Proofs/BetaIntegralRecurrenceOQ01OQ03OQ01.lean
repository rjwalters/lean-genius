/-
# Beta Integral OQ-01 (leaf oq-03-oq-01): the off-diagonal real Euler Beta integral

The parent leaf `BetaIntegralRecurrenceOQ01OQ03` supplied the **diagonal** real integral
`∫₀¹ xⁿ(1-x)ⁿ dx = (n!)²/(2n+1)!`. This leaf supplies the full **off-diagonal** real
Euler Beta integral at integer arguments:

  `∫₀¹ xᵐ(1-x)ⁿ dx = m!·n! / (m+n+1)!`.

It is proved **two independent ways**, which is the point of the entry:

1. `integral_offdiag_eq_factorial` — via the complex bridge.  Cast the real integral into
   ℂ, recognise it as `Complex.betaIntegral (m+1) (n+1)` (the integrand `x^(u-1)(1-x)^(v-1)`
   collapses to monoid powers on `[0,1]` via `Complex.cpow_natCast`), and read off the
   closed form from the parent's `betaIntegral_nat_nat`.  This generalises the parent's
   diagonal bridge `ofReal_integral_diag` to `m ≠ n`.

2. `integral_offdiag_via_ibp` — a **self-contained real-analysis proof** that never leaves
   ℝ.  The single recurrence

     `integral_recurrence : ∫₀¹ xᵐ(1-x)ⁿ⁺¹ = ((n+1)/(m+1))·∫₀¹ xᵐ⁺¹(1-x)ⁿ`

   is genuine integration by parts (`integral_mul_deriv_eq_deriv_mul`, boundary terms
   vanish), and induction on `n` down to the base `∫₀¹ xᵐ⁺ⁿ = 1/(m+n+1)` gives the closed
   form independently of Mathlib's `Complex.Gamma`.  `agreement` checks the two routes
   coincide.

Neither the off-diagonal real integral nor this recurrence is in Mathlib (which has only the
complex analytic `betaIntegral`).

*Reference:* Euler Beta function at integer arguments; Mathlib
`Mathlib.Analysis.SpecialFunctions.Gamma.Beta`.
-/

import Proofs.BetaIntegralRecurrence
import Mathlib.Tactic

open Complex intervalIntegral MeasureTheory

namespace BetaIntegralRecurrenceOQ01OQ03OQ01

/-! ## Route 1 — the complex bridge -/

/-- **Bridge to the real line, off-diagonal.** The complex Beta integral `B(m+1,n+1)` is the
real integral of `xᵐ(1-x)ⁿ`, cast into ℂ.  On `[0,1]` the complex powers
`(x:ℂ)^((m+1)-1)`, `(1-x)^((n+1)-1)` collapse to monoid powers via `Complex.cpow_natCast`,
and the integral descends through `ofReal`. -/
theorem ofReal_integral_offdiag (m n : ℕ) :
    (((∫ x in (0:ℝ)..1, x ^ m * (1 - x) ^ n) : ℝ) : ℂ)
      = betaIntegral ((m : ℂ) + 1) ((n : ℂ) + 1) := by
  rw [betaIntegral, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  have hm : ((m : ℂ) + 1) - 1 = (m : ℂ) := by ring
  have hn : ((n : ℂ) + 1) - 1 = (n : ℂ) := by ring
  rw [hm, hn, Complex.cpow_natCast, Complex.cpow_natCast]
  push_cast
  ring

/-- **The off-diagonal real Euler Beta integral.**
`∫₀¹ xᵐ(1-x)ⁿ dx = m!·n! / (m+n+1)!`.  Proof via the complex closed form. -/
theorem integral_offdiag_eq_factorial (m n : ℕ) :
    ∫ x in (0:ℝ)..1, x ^ m * (1 - x) ^ n
      = (m.factorial : ℝ) * (n.factorial : ℝ) / ((m + n + 1).factorial : ℝ) := by
  have h := ofReal_integral_offdiag m n
  rw [BetaIntegralRecurrence.betaIntegral_nat_nat m n] at h
  have hrhs :
      (m.factorial : ℂ) * (n.factorial : ℂ) / ((m + n + 1).factorial : ℂ)
        = (((m.factorial : ℝ) * (n.factorial : ℝ) / ((m + n + 1).factorial : ℝ)) : ℂ) := by
    push_cast; ring
  rw [hrhs] at h
  exact_mod_cast h

/-! ## Route 2 — a self-contained real integration-by-parts proof -/

/-- **Base case.** `∫₀¹ xᵏ(1-x)⁰ = 1/(k+1)`, i.e. `∫₀¹ xᵏ = 1/(k+1)`. -/
theorem integral_base (k : ℕ) :
    ∫ x in (0:ℝ)..1, x ^ k * (1 - x) ^ 0 = 1 / ((k : ℝ) + 1) := by
  simp only [pow_zero, mul_one]
  rw [integral_pow]
  simp

/-- **Integration-by-parts recurrence (pure real analysis).**
`∫₀¹ xᵐ(1-x)ⁿ⁺¹ = ((n+1)/(m+1)) · ∫₀¹ xᵐ⁺¹(1-x)ⁿ`.

Integrate by parts with `u = (1-x)ⁿ⁺¹`, `v = xᵐ⁺¹/(m+1)`; both boundary terms vanish. -/
theorem integral_recurrence (m n : ℕ) :
    ∫ x in (0:ℝ)..1, x ^ m * (1 - x) ^ (n + 1)
      = ((n : ℝ) + 1) / ((m : ℝ) + 1) * ∫ x in (0:ℝ)..1, x ^ (m + 1) * (1 - x) ^ n := by
  -- derivative of u = (1-x)^(n+1)
  have hu : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun y : ℝ => (1 - y) ^ (n + 1))
        (((n : ℝ) + 1) * (1 - x) ^ n * (-1)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    have h2 := h1.pow (n + 1)
    simp only [Nat.add_sub_cancel] at h2
    convert h2 using 1
    push_cast; ring
  -- derivative of v = x^(m+1)/(m+1)
  have hv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun y : ℝ => y ^ (m + 1) / ((m : ℝ) + 1)) (x ^ m) x := by
    intro x _
    have h := (hasDerivAt_pow (m + 1) x).div_const ((m : ℝ) + 1)
    simp only [Nat.add_sub_cancel] at h
    convert h using 1
    push_cast
    field_simp
  have hu' : IntervalIntegrable (fun x => ((n : ℝ) + 1) * (1 - x) ^ n * (-1)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hv' : IntervalIntegrable (fun x : ℝ => x ^ m) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have key := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  -- rewrite the target integrand into the IBP order  u * v'
  rw [show (∫ x in (0:ℝ)..1, x ^ m * (1 - x) ^ (n + 1))
        = ∫ x in (0:ℝ)..1, (1 - x) ^ (n + 1) * x ^ m from
        integral_congr (fun x _ => by ring)]
  rw [key]
  -- boundary terms vanish
  have e1 : ((1:ℝ) - 1) ^ (n + 1) = 0 := by rw [sub_self]; exact zero_pow (Nat.succ_ne_zero n)
  have e2 : ((0:ℝ)) ^ (m + 1) = 0 := zero_pow (Nat.succ_ne_zero m)
  rw [e1, e2]
  -- pull the constant out of the remaining integral
  rw [show (∫ x in (0:ℝ)..1,
            ((n : ℝ) + 1) * (1 - x) ^ n * (-1) * (x ^ (m + 1) / ((m : ℝ) + 1)))
        = ∫ x in (0:ℝ)..1,
            (-(((n : ℝ) + 1) / ((m : ℝ) + 1))) * (x ^ (m + 1) * (1 - x) ^ n) from
        integral_congr (fun x _ => by ring)]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- **The off-diagonal real Euler Beta integral, proved without leaving ℝ.**
Induction on `n` via `integral_recurrence`, base case `integral_base`. -/
theorem integral_offdiag_via_ibp (m n : ℕ) :
    ∫ x in (0:ℝ)..1, x ^ m * (1 - x) ^ n
      = (m.factorial : ℝ) * (n.factorial : ℝ) / ((m + n + 1).factorial : ℝ) := by
  induction n generalizing m with
  | zero =>
    rw [integral_base m]
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one, Nat.add_zero]
    have hfac : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hmf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
    have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
    rw [hfac]
    field_simp
  | succ n ih =>
    rw [integral_recurrence m n, ih (m + 1)]
    -- ((n+1)/(m+1)) * ((m+1)! (n)! / (m+1+n+1)!) = m! (n+1)! / (m+(n+1)+1)!
    have hm1 : ((m + 1).factorial : ℝ) = (m.factorial : ℝ) * ((m : ℝ) + 1) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hn1 : ((n + 1).factorial : ℝ) = (n.factorial : ℝ) * ((n : ℝ) + 1) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hidx : m + 1 + n + 1 = m + (n + 1) + 1 := by ring
    have hmpos : (0:ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hfac : (0:ℝ) < ((m + (n + 1) + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    rw [hidx, hm1, hn1]
    field_simp

/-- **Symmetry `m ↔ n`** of the off-diagonal Beta integral, read off the closed form. -/
theorem integral_offdiag_symm (m n : ℕ) :
    (∫ x in (0:ℝ)..1, x ^ m * (1 - x) ^ n)
      = ∫ x in (0:ℝ)..1, x ^ n * (1 - x) ^ m := by
  rw [integral_offdiag_eq_factorial, integral_offdiag_eq_factorial,
      Nat.add_comm n m]
  ring

end BetaIntegralRecurrenceOQ01OQ03OQ01
