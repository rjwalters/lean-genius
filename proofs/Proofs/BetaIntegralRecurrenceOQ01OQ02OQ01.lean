import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-
# The Symmetric Beta Value at Half-Integers: `B(n+½, n+½) = π·C(2n,n)/4^{2n}`

## What This Proves

The sibling entry `beta-integral-recurrence-oq-01-oq-02` computed the first two
half-integer Beta values `B(½,½) = π` and `B(3/2,3/2) = π/8` one at a time. This
entry closes the **entire diagonal** in one formula:

  **`betaIntegral_diag_half`**:
    `B(n+½, n+½) = π · (2n)! / (4^{2n} · (n!)²)`,

equivalently (`betaIntegral_diag_half_centralBinom`):

    `B(n+½, n+½) = π · C(2n, n) / 4^{2n}`

with `C(2n,n) = Nat.centralBinom n` the central binomial coefficient.

## A striking contrast

The gallery already has the **integer** diagonal
(`BetaCentralBinomial.betaIntegral_diag_central_binom`):

    `B(n+1, n+1) = 1 / ((2n+1) · C(2n, n))`,

a *rational* number with the central binomial in the **denominator**. The
half-integer diagonal is its mirror image: a *transcendental* multiple of `π`
with the very same central binomial in the **numerator**. The two diagonals of
the Beta lattice are governed by reciprocal appearances of `C(2n,n)`.

Setting `n = 0` recovers `B(½,½) = π` and `n = 1` recovers `B(3/2,3/2) = π/8`
(`C(0,0)=1`, `C(2,1)=2`, `4²=16`, `2/16 = 1/8`), so this single theorem subsumes
both values proved separately in the sibling entry.

## Relation to Mathlib

Mathlib provides the Beta–Gamma division formula
`Complex.betaIntegral_eq_Gamma_mul_div`, the real/complex bridge
`Complex.Gamma_ofReal`, `Complex.Gamma_nat_eq_factorial`, and the half-integer
Gamma value `Real.Gamma_nat_add_half` (in *double-factorial* form
`Γ(k+½) = (2k-1)‼·√π / 2^k`). It does **not** state the factorial form of
`Γ(n+½)`, nor any half-integer Beta value. The new content here is:

  * `gamma_nat_add_half_eq` : the **factorial closed form**
    `Γ(n+½) = √π · (2n)! / (4^n · n!)`, proved directly by induction on the
    Gamma functional equation `Γ(s+1) = s·Γ(s)` (independent of Mathlib's
    double-factorial route); and
  * the assembly of the diagonal Beta value from it.

## Approach

`gamma_nat_add_half_eq` is an induction: the base case is the Gauss value
`Γ(½) = √π`, and the step multiplies by `(n+½)` via `Real.Gamma_add_one`,
matching `(2n+2)(2n+1)/(4(n+1)) = (2n+1)/2 = (n+½)` on the closed form.

`betaIntegral_diag_half` then applies `betaIntegral_eq_Gamma_mul_div` (both real
parts are `n+½ > 0`), rewrites the argument sum `(n+½)+(n+½) = (2n)+1` so the
denominator collapses to `Γ(2n+1) = (2n)!`, transfers each `Γ(n+½)` to the real
line via `Gamma_ofReal`, substitutes the closed form, and finishes with a real
field computation using `√π·√π = π` and `4^{2n} = (4^n)²`.
-/

namespace BetaIntegralRecurrenceOQ01OQ02OQ01

open scoped Nat
open Real

/-- **Factorial closed form of the half-integer Gamma value (new).**

`Γ(n + ½) = √π · (2n)! / (4ⁿ · n!)`.

Proved by induction on `n` using only the Gauss value `Γ(½) = √π` and the
functional equation `Γ(s+1) = s·Γ(s)`; this is the factorial counterpart of
Mathlib's double-factorial `Real.Gamma_nat_add_half`. -/
theorem gamma_nat_add_half_eq (n : ℕ) :
    Real.Gamma ((n : ℝ) + 1 / 2) = Real.sqrt π * (2 * n)! / (4 ^ n * n !) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_add, Real.Gamma_one_half_eq]
    norm_num
  | succ k ih =>
    have hk : ((k : ℝ) + 1 / 2) ≠ 0 := by positivity
    have hrec : Real.Gamma ((k : ℝ) + 1 / 2 + 1)
        = ((k : ℝ) + 1 / 2) * Real.Gamma ((k : ℝ) + 1 / 2) := Real.Gamma_add_one hk
    have hcast : (((k + 1 : ℕ) : ℝ) + 1 / 2) = ((k : ℝ) + 1 / 2) + 1 := by push_cast; ring
    -- factorials of the successor, computed in ℕ then cast to ℝ
    have hf : ((2 * (k + 1))! : ℝ) = (2 * k + 2) * ((2 * k + 1) * (2 * k)!) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ,
        Nat.factorial_succ (2 * k)]
      push_cast; ring
    have hnf : ((k + 1)! : ℝ) = ((k : ℝ) + 1) * k ! := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hkfac : ((k ! : ℝ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    have h4k : (4 : ℝ) ^ k ≠ 0 := by positivity
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [hcast, hrec, ih, hf, hnf]
    field_simp
    ring

/-- **The symmetric half-integer Beta value (new).**

`B(n+½, n+½) = π · (2n)! / (4^{2n} · (n!)²)`. The full diagonal of half-integer
Beta values, subsuming the sibling entry's `B(½,½)=π` and `B(3/2,3/2)=π/8`. -/
theorem betaIntegral_diag_half (n : ℕ) :
    Complex.betaIntegral ((n : ℂ) + 1 / 2) ((n : ℂ) + 1 / 2)
      = (π : ℂ) * (2 * n)! / (4 ^ (2 * n) * (n ! : ℂ) ^ 2) := by
  have hre : (0 : ℝ) < ((n : ℂ) + 1 / 2).re := by
    simp; positivity
  -- The real value of `Γ(n+½)²/(2n)!`.
  have hreal : Real.Gamma ((n : ℝ) + 1 / 2) ^ 2 / ((2 * n)! : ℝ)
      = π * (2 * n)! / (4 ^ (2 * n) * (n ! : ℝ) ^ 2) := by
    rw [gamma_nat_add_half_eq]
    have hsqrt : Real.sqrt π ^ 2 = π := Real.sq_sqrt Real.pi_nonneg
    have h4 : (4 : ℝ) ^ (2 * n) = (4 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
    have hn : ((n ! : ℝ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    have hfac : ((2 * n)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (2 * n)).ne'
    have h4n : (4 : ℝ) ^ n ≠ 0 := by positivity
    simp only [div_pow, mul_pow]
    rw [hsqrt, h4]
    field_simp
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hre hre,
    show ((n : ℂ) + 1 / 2) + ((n : ℂ) + 1 / 2) = ((2 * n : ℕ) : ℂ) + 1 by push_cast; ring,
    Complex.Gamma_nat_eq_factorial,
    show ((n : ℂ) + 1 / 2) = (((n : ℝ) + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal]
  rw [show (((Real.Gamma ((n : ℝ) + 1 / 2) : ℝ) : ℂ)
        * ((Real.Gamma ((n : ℝ) + 1 / 2) : ℝ) : ℂ) / ((2 * n)! : ℂ))
      = (((Real.Gamma ((n : ℝ) + 1 / 2) ^ 2 / ((2 * n)! : ℝ) : ℝ)) : ℂ) by
    push_cast; ring]
  rw [hreal]
  push_cast
  ring

/-- The same value with Mathlib's central binomial coefficient:
`B(n+½, n+½) = π · C(2n, n) / 4^{2n}`.

The mirror of the integer diagonal `B(n+1,n+1) = 1/((2n+1)·C(2n,n))`: here the
central binomial sits in the **numerator**, scaled by the transcendental `π`. -/
theorem betaIntegral_diag_half_centralBinom (n : ℕ) :
    Complex.betaIntegral ((n : ℂ) + 1 / 2) ((n : ℂ) + 1 / 2)
      = (π : ℂ) * (Nat.centralBinom n : ℂ) / 4 ^ (2 * n) := by
  rw [betaIntegral_diag_half]
  have hbinom : ((2 * n)! : ℂ) = (Nat.centralBinom n : ℂ) * ((n ! : ℂ) ^ 2) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose]
    have : (2 * n)! = (2 * n).choose n * n ! * n ! := by rw [h]
    rw [this]; push_cast; ring
  rw [hbinom]
  have hn : ((n ! : ℂ)) ≠ 0 := by
    have : (0 : ℕ) < n ! := Nat.factorial_pos n
    exact_mod_cast this.ne'
  field_simp

/-- Sanity check: `n = 0` recovers the sibling entry's `B(½,½) = π`. -/
theorem betaIntegral_half_half : Complex.betaIntegral (1 / 2) (1 / 2) = (π : ℂ) := by
  have h := betaIntegral_diag_half_centralBinom 0
  norm_num [Nat.centralBinom] at h
  simpa using h

/-- Sanity check: `n = 1` recovers the sibling entry's `B(3/2, 3/2) = π/8`. -/
theorem betaIntegral_three_half_three_half :
    Complex.betaIntegral (3 / 2) (3 / 2) = (π : ℂ) / 8 := by
  have h := betaIntegral_diag_half_centralBinom 1
  norm_num [Nat.centralBinom, Nat.choose] at h
  rw [h]; ring

end BetaIntegralRecurrenceOQ01OQ02OQ01
