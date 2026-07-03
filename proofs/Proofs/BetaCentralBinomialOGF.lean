import Proofs.BetaCentralBinomial
import Mathlib.Tactic

/-
# The Central Beta Sequence and its Ordinary Generating Function

## What This Proves

The parent entries establish the integer closed form of the Euler Beta integral
`B(m+1,n+1) = m!·n!/(m+n+1)!` (`betaIntegral_nat_nat`) and its **diagonal**
value as a central-binomial reciprocal
`B(n+1,n+1) = 1/((2n+1)·C(2n,n))` (`betaIntegral_diag_central_binom`).

This file studies the *diagonal sequence itself*,

  `b(n) := B(n+1,n+1) = (n!)² / (2n+1)! = 1 / ((2n+1)·C(2n,n))`,

as the coefficient sequence of a power series, and pins down its arithmetic
structure — the data that determines its ordinary generating function.

The headline result is the **two-term contiguous recurrence**

  **`centralBeta_recurrence`**:  `(4n+6) · b(n+1) = (n+1) · b(n)`.

Together with the initial value `b(0) = 1` (`centralBeta_zero`) this recurrence
*characterizes* the sequence, and hence its generating function
`y(x) = Σₙ b(n) xⁿ`: translating the recurrence coefficient-by-coefficient shows
`y` solves the first-order linear ODE `x(4-x) y'(x) + (2-x) y(x) = 2`,
`y(0) = 1`, whose closed-form solution is

  `Σₙ b(n) xⁿ = 4·arcsin(√x / 2) / √(x(4-x))`   (0 < x < 4),

the classical reciprocal-central-binomial generating function (value `π/2` at
`x = 2`). The analytic identity — interchanging the sum with the Beta integral
`b(n) = ∫₀¹ (t(1-t))ⁿ dt` and evaluating `∫₀¹ dt/(1 - x t(1-t))` — is recorded
here as the stated sequel; this file supplies the *verified arithmetic backbone*
(reciprocal form, gallery link, recurrence, base values) on which that analytic
proof rests.

## Relation to Mathlib

Mathlib provides `Nat.centralBinom`, `Nat.choose_mul_factorial_mul_factorial`,
and `Real.arcsin`, but states neither the diagonal Beta value nor its
generating function. We build `b(n)` over `ℝ`, connect it to the parent's
complex Beta value by a cast, and derive the recurrence from a single factorial
identity.
-/

namespace BetaCentralBinomialOGF

open scoped Nat
open Complex

/-- The **central Beta sequence** `b(n) = (n!)² / (2n+1)!`, the diagonal value
`B(n+1, n+1)` of the Euler Beta integral, viewed as a real sequence. -/
noncomputable def centralBeta (n : ℕ) : ℝ :=
    (n ! * n ! : ℝ) / (2 * n + 1)!

/-- `b(0) = 1`. -/
theorem centralBeta_zero : centralBeta 0 = 1 := by
  simp [centralBeta]

/-- `b(1) = 1/6`. -/
theorem centralBeta_one : centralBeta 1 = 1 / 6 := by
  norm_num [centralBeta, Nat.factorial]

/-- `b(2) = 1/30`. -/
theorem centralBeta_two : centralBeta 2 = 1 / 30 := by
  norm_num [centralBeta, Nat.factorial]

/-- The sequence is strictly positive. -/
theorem centralBeta_pos (n : ℕ) : 0 < centralBeta n := by
  unfold centralBeta
  have hnum : (0 : ℝ) < (n ! * n ! : ℝ) := by
    have := Nat.factorial_pos n
    positivity
  have hden : (0 : ℝ) < ((2 * n + 1)! : ℝ) := by
    have := Nat.factorial_pos (2 * n + 1)
    exact_mod_cast this
  positivity

/-- **Reciprocal / central-binomial form.**  `b(n) = 1 / ((2n+1)·C(2n,n))`,
matching the parent entry's `betaIntegral_diag_central_binom`. -/
theorem centralBeta_eq_reciprocal (n : ℕ) :
    centralBeta n = 1 / (((2 * n + 1) * (2 * n).choose n : ℕ) : ℝ) := by
  have hM : ((((2 * n + 1) * (2 * n).choose n : ℕ) : ℝ)) ≠ 0 := by
    have : 0 < (2 * n + 1) * (2 * n).choose n := by
      have := Nat.choose_pos (show n ≤ 2 * n by omega); positivity
    exact_mod_cast this.ne'
  have hN : ((n ! : ℝ) * (n ! : ℝ)) ≠ 0 := by
    have := Nat.factorial_pos n; positivity
  have hfacR : ((2 * n + 1)! : ℝ)
      = (((2 * n + 1) * (2 * n).choose n : ℕ) : ℝ) * ((n ! : ℝ) * (n ! : ℝ)) := by
    have h := BetaCentralBinomial.factorial_two_mul_succ n
    rw [h]; push_cast; ring
  rw [centralBeta, hfacR]
  field_simp

/-- **Link to the gallery Beta integral.**  As a complex number, `b(n)` is
exactly the diagonal Euler Beta value `B(n+1, n+1)`. -/
theorem centralBeta_eq_betaIntegral (n : ℕ) :
    ((centralBeta n : ℝ) : ℂ) = betaIntegral ((n : ℂ) + 1) ((n : ℂ) + 1) := by
  rw [BetaCentralBinomial.betaIntegral_diag_central_binom,
      centralBeta_eq_reciprocal]
  push_cast
  ring

/-- The factorial identity underlying the recurrence, over `ℕ`:

  `(4n+6) · (n+1)!² · (2n+1)! = (n+1) · n!² · (2(n+1)+1)!`.

Both sides expand, via `Nat.factorial_succ`, to `(4n+6)(n+1)² · n!² · (2n+1)!`. -/
theorem centralBeta_factorial_identity (n : ℕ) :
    (4 * n + 6) * ((n + 1)! * (n + 1)!) * (2 * n + 1)!
      = (n + 1) * (n ! * n !) * (2 * (n + 1) + 1)! := by
  have e1 : (n + 1)! = (n + 1) * n ! := Nat.factorial_succ n
  have e2 : (2 * (n + 1) + 1)! = (2 * n + 3) * ((2 * n + 2) * (2 * n + 1)!) := by
    have h3 : 2 * (n + 1) + 1 = (2 * n + 2) + 1 := by ring
    have h2 : 2 * n + 2 = (2 * n + 1) + 1 := by ring
    rw [h3, Nat.factorial_succ, h2, Nat.factorial_succ]
  rw [e1, e2]; ring

/-- **The contiguous recurrence (new).**  `(4n+6) · b(n+1) = (n+1) · b(n)`.

Equivalently `b(n+1) = (n+1)/(2(2n+3)) · b(n)`. This is the arithmetic engine
of the generating function: it is the coefficient form of the ODE
`x(4-x) y' + (2-x) y = 2` satisfied by `y(x) = Σ b(n) xⁿ`. -/
theorem centralBeta_recurrence (n : ℕ) :
    (4 * (n : ℝ) + 6) * centralBeta (n + 1) = ((n : ℝ) + 1) * centralBeta n := by
  have h1 : ((2 * n + 1)! : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (2 * n + 1)).ne'
  have h2 : ((2 * (n + 1) + 1)! : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (2 * (n + 1) + 1)).ne'
  have hkey := centralBeta_factorial_identity n
  have hkeyR : (4 * (n : ℝ) + 6) * (((n + 1)! : ℝ) * ((n + 1)! : ℝ)) * ((2 * n + 1)! : ℝ)
      = ((n : ℝ) + 1) * ((n ! : ℝ) * (n ! : ℝ)) * ((2 * (n + 1) + 1)! : ℝ) := by
    exact_mod_cast hkey
  unfold centralBeta
  rw [← mul_div_assoc, ← mul_div_assoc, div_eq_div_iff h2 h1]
  linear_combination hkeyR

/-!
## The closed-form generating function

We now discharge the analytic result that the arithmetic backbone above was built
to support: the **closed form of the ordinary generating function**
`y(x) = Σₙ b(n) xⁿ`. Interchanging the sum with the Beta integral
`b(n) = ∫₀¹ (t(1-t))ⁿ dt` and summing the geometric series gives

  `y(x) = ∫₀¹ dt / (1 - x·t(1-t))`,

and this kernel integral has the closed form

  **`centralBeta_ogf_kernel_integral`**:
    `∫₀¹ dt/(1 - x·t(1-t)) = 4·arcsin(√x/2) / √(x(4-x))`   for `0 < x < 4`.

The evaluation is a clean application of the fundamental theorem of calculus with
antiderivative `F(t) = (2/√(x(4-x)))·arctan((2xt - x)/√(x(4-x)))`, whose derivative
is exactly the kernel `1/(1 - x·t(1-t))` (the identity
`√(x(4-x))² + (2xt-x)² = 4x(1 - x·t(1-t))` collapses the `arctan` derivative to the
kernel), and the boundary evaluation `F(1) - F(0) = (4/√(x(4-x)))·arctan(x/√(x(4-x)))`
followed by the trigonometric bridge `arctan(x/√(x(4-x))) = arcsin(√x/2)`.
-/

/-- **Trigonometric bridge.**  For `0 < x < 4`,
`arctan(x / √(x(4-x))) = arcsin(√x / 2)`.

Both sides lie in `(-π/2, π/2)`, and their tangents agree: writing `s = √x/2`,
`tan(arcsin s) = s/√(1 - s²) = (√x/2)/(√(4-x)/2) = √x/√(4-x) = x/√(x(4-x))`. -/
theorem arctan_div_sqrt_eq_arcsin {x : ℝ} (hx0 : 0 < x) (hx4 : x < 4) :
    Real.arctan (x / Real.sqrt (x * (4 - x))) = Real.arcsin (Real.sqrt x / 2) := by
  have h4x : (0 : ℝ) < 4 - x := by linarith
  have hsxpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsx4pos : 0 < Real.sqrt (4 - x) := Real.sqrt_pos.mpr h4x
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hprod : Real.sqrt (x * (4 - x)) = Real.sqrt x * Real.sqrt (4 - x) :=
    Real.sqrt_mul hx0.le _
  set s := Real.sqrt x / 2 with hs
  have hs_nonneg : 0 ≤ s := by positivity
  have hs_lt1 : s < 1 := by
    rw [hs, div_lt_one (by norm_num)]
    have hlt : Real.sqrt x < Real.sqrt 4 := Real.sqrt_lt_sqrt hx0.le hx4
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)] at hlt
  -- `√(1 - s²) = √(4-x)/2`
  have hs2 : (1 : ℝ) - s ^ 2 = (4 - x) / 4 := by
    rw [hs, div_pow, hxx]; ring
  have hsqrt_half : Real.sqrt (1 - s ^ 2) = Real.sqrt (4 - x) / 2 := by
    rw [hs2, show (4 - x) / 4 = (4 - x) * (1 / 4) by ring, Real.sqrt_mul h4x.le,
      show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    ring
  -- the two tangents agree
  have hkey : x / Real.sqrt (x * (4 - x)) = Real.tan (Real.arcsin s) := by
    rw [Real.tan_arcsin, hsqrt_half, hprod, hs, div_div_div_cancel_right₀,
      div_eq_div_iff (by positivity) (by positivity)]
    nlinarith [hxx, hsxpos, hsx4pos]
  rw [hkey, Real.arctan_tan]
  · exact Real.neg_pi_div_two_lt_arcsin.mpr (by linarith)
  · exact Real.arcsin_lt_pi_div_two.mpr hs_lt1

/-- **Closed-form OGF kernel integral (new).**  For `0 < x < 4`,

  `∫₀¹ dt / (1 - x·t(1-t)) = 4·arcsin(√x/2) / √(x(4-x))`.

This is the definite integral obtained after interchanging `Σₙ b(n) xⁿ` with the
Beta integral `b(n) = ∫₀¹ (t(1-t))ⁿ dt` and summing the geometric series; it is the
closed form of the ordinary generating function of the central Beta sequence. -/
theorem centralBeta_ogf_kernel_integral {x : ℝ} (hx0 : 0 < x) (hx4 : x < 4) :
    ∫ t in (0 : ℝ)..1, (1 - x * t * (1 - t))⁻¹
      = 4 * Real.arcsin (Real.sqrt x / 2) / Real.sqrt (x * (4 - x)) := by
  have hxpos : 0 < x * (4 - x) := mul_pos hx0 (by linarith)
  set k := Real.sqrt (x * (4 - x)) with hk
  have hkpos : 0 < k := Real.sqrt_pos.mpr hxpos
  have hkne : k ≠ 0 := ne_of_gt hkpos
  have hk2 : k ^ 2 = x * (4 - x) := Real.sq_sqrt hxpos.le
  -- denominator positive on the interval
  have hden : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < 1 - x * t * (1 - t) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    obtain ⟨h0, h1⟩ := ht
    nlinarith [mul_nonneg hx0.le (sq_nonneg (2 * t - 1)), hx4]
  -- the antiderivative has the kernel as derivative
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t => (2 / k) * Real.arctan ((2 * x * t - x) / k))
        ((1 - x * t * (1 - t))⁻¹) t := by
    intro t ht
    have hden_t : 0 < 1 - x * t * (1 - t) := hden t ht
    have hg : HasDerivAt (fun t : ℝ => (2 * x * t - x) / k) (2 * x / k) t := by
      have h0 : HasDerivAt (fun t : ℝ => 2 * x * t - x) (2 * x) t := by
        simpa using ((hasDerivAt_id t).const_mul (2 * x)).sub_const x
      simpa using h0.div_const k
    have harc : HasDerivAt (fun t => Real.arctan ((2 * x * t - x) / k))
        ((1 / (1 + ((2 * x * t - x) / k) ^ 2)) * (2 * x / k)) t :=
      (Real.hasDerivAt_arctan ((2 * x * t - x) / k)).comp t hg
    have hF' : HasDerivAt (fun t => (2 / k) * Real.arctan ((2 * x * t - x) / k))
        ((2 / k) * ((1 / (1 + ((2 * x * t - x) / k) ^ 2)) * (2 * x / k))) t :=
      harc.const_mul (2 / k)
    have hg2 : (1 : ℝ) + ((2 * x * t - x) / k) ^ 2
        = (k ^ 2 + (2 * x * t - x) ^ 2) / k ^ 2 := by
      rw [div_pow, add_div, div_self (pow_ne_zero 2 hkne)]
    have hPne : k ^ 2 + (2 * x * t - x) ^ 2 ≠ 0 := by positivity
    have hRHS : (2 / k) * ((1 / (1 + ((2 * x * t - x) / k) ^ 2)) * (2 * x / k))
        = 4 * x / (k ^ 2 + (2 * x * t - x) ^ 2) := by
      rw [hg2, one_div_div]; field_simp; ring
    have hP : k ^ 2 + (2 * x * t - x) ^ 2 = 4 * x * (1 - x * t * (1 - t)) := by
      rw [hk2]; ring
    have hPpos : 0 < 4 * x * (1 - x * t * (1 - t)) :=
      mul_pos (mul_pos (by norm_num) hx0) hden_t
    have hw : (1 - x * t * (1 - t)) ≠ 0 := ne_of_gt hden_t
    have hval : (1 - x * t * (1 - t))⁻¹
        = (2 / k) * ((1 / (1 + ((2 * x * t - x) / k) ^ 2)) * (2 * x / k)) := by
      rw [hRHS, hP, inv_eq_one_div, div_eq_div_iff hw (ne_of_gt hPpos)]; ring
    rw [hval]; exact hF'
  -- integrability of the kernel on the interval
  have hcont : ContinuousOn (fun t => (1 - x * t * (1 - t))⁻¹) (Set.uIcc (0 : ℝ) 1) := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro t ht; exact (hden t ht).ne'
  have hint : IntervalIntegrable (fun t => (1 - x * t * (1 - t))⁻¹)
      MeasureTheory.volume 0 1 := hcont.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  -- boundary evaluation
  simp only []
  rw [show (2 * x * 1 - x) = x by ring, show (2 * x * 0 - x) = -x by ring,
      neg_div, Real.arctan_neg, hk, arctan_div_sqrt_eq_arcsin hx0 hx4]
  ring

end BetaCentralBinomialOGF
