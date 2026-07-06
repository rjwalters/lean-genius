import Mathlib
import Proofs.BetaCentralBinomialAsymptotic

/-
# An Effective Two-Sided Rate for the Diagonal Beta Value (OQ-01…-OQ-01)

## The Open Question

`BetaCentralBinomialAsymptotic.lean` proves the *asymptotic*

  B(n+1, n+1) = betaDiag n  ~  √(πn) / ((2n+1)·4ⁿ)      (as n → ∞)

as an `Asymptotics.IsEquivalent` statement (`betaDiag_isEquivalent`).  Its first
listed open question asks to **upgrade the `~` to an explicit two-sided rate with
effective constants**, using the fact — already in Mathlib — that
`√π ≤ stirlingSeq n` for every `n ≠ 0`.

## What This File Proves

Write the *ratio* of the true value to the target as

  ratioR n  :=  stirlingSeq n ² / (√π · stirlingSeq (2n)),

so that (Part II) for every `n ≥ 1`

  betaDiag n  =  √(πn) / ((2n+1)·4ⁿ)  ·  ratioR n.                 -- betaDiag_eq

This makes the correction factor completely explicit.  Mathlib's *effective*
Stirling bounds — `√π ≤ stirlingSeq n` (a genuine lower bound for all `n ≥ 1`)
and antitonicity giving `stirlingSeq n ≤ stirlingSeq 1 = e/√2` — pin `ratioR` to
an explicit interval (Part III):

  √(2π)/e  ≤  ratioR n  ≤  e²/(2π)        for every n ≥ 1,          -- ratioR_ge / ratioR_le

with `ratioR n → 1` (Part IV, `ratioR_tendsto_one`).  Feeding the interval into
`betaDiag_eq` yields the requested **effective two-sided rate** (Part V):

  (√(2π)/e) · √(πn)/((2n+1)·4ⁿ)  ≤  betaDiag n  ≤  (e²/(2π)) · √(πn)/((2n+1)·4ⁿ).

Numerically the constants are `√(2π)/e ≈ 0.922` and `e²/(2π) ≈ 1.176`, and both
hold for **all** `n ≥ 1` — an effective, if not asymptotically sharp, envelope.

## Honest Scope

These are **constant-factor** two-sided bounds, valid for all `n ≥ 1`.  The
sharper `1 + O(1/n)` form with the optimal constant would require the Robbins
refinement of Stirling's series, which Mathlib notes is *not yet formalised*
(`Stirling.le_factorial_stirling` docstring).  The core exact identity
`centralBinom n = stirlingSeq (2n) / stirlingSeq n ² · 4ⁿ/√n` (Part I) is proved
here from Mathlib's `stirlingSeq` definition with 0 axioms.
-/

namespace BetaDiagEffectiveRate

open Real Filter Asymptotics Stirling BetaDiagAsymptotic
open scoped Topology Nat

/-!
## Part I: The exact Stirling identity for the central binomial coefficient

`centralBinom n · √n · stirlingSeq n ² = stirlingSeq (2n) · 4ⁿ`, equivalently
`centralBinom n = stirlingSeq (2n)/stirlingSeq n ² · 4ⁿ/√n`.  This is pure algebra
from `stirlingSeq n = n!/(√(2n)·(n/e)ⁿ)`; the `4ⁿ` comes from
`(2n/e)^{2n} = 4ⁿ·((n/e)ⁿ)²`.
-/

/-- **Exact central-binomial / Stirling identity.** -/
theorem centralBinom_stirlingSeq (n : ℕ) (hn : n ≠ 0) :
    (Nat.centralBinom n : ℝ) * Real.sqrt n * stirlingSeq n ^ 2
      = stirlingSeq (2 * n) * 4 ^ n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  -- √(2·(2n)) = 2·√n
  have hA : Real.sqrt (2 * ((2 * n : ℕ) : ℝ)) = 2 * Real.sqrt (n : ℝ) := by
    push_cast
    rw [show (2 : ℝ) * (2 * (n : ℝ)) = 2 ^ 2 * (n : ℝ) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]
  -- (2n/e)^{2n} = 4ⁿ·((n/e)ⁿ)²
  have hB : (((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n)
      = 4 ^ n * (((n : ℝ) / Real.exp 1) ^ n) ^ 2 := by
    push_cast
    have h2 : (2 : ℝ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
    rw [show (2 * (n : ℝ)) / Real.exp 1 = 2 * ((n : ℝ) / Real.exp 1) by rw [mul_div_assoc],
        mul_pow, h2, ← pow_mul, Nat.mul_comm n 2]
  -- centralBinom·(n!·n!) = (2n)!
  have hfac : (Nat.centralBinom n : ℝ) * ((n ! : ℝ) * (n ! : ℝ)) = ((2 * n)! : ℝ) := by
    have h : Nat.centralBinom n * (n ! * n !) = (2 * n)! := by
      have hh := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
      rw [show 2 * n - n = n by omega] at hh
      simpa [Nat.centralBinom, mul_assoc] using hh
    exact_mod_cast h
  -- explicit values of the two Stirling terms
  have hval_n : stirlingSeq n
      = (n ! : ℝ) / (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := rfl
  have hval_2n : stirlingSeq (2 * n)
      = ((2 * n)! : ℝ) / (2 * Real.sqrt (n : ℝ) * (4 ^ n * (((n : ℝ) / Real.exp 1) ^ n) ^ 2)) := by
    rw [stirlingSeq, hA, hB]
  have hP : (0 : ℝ) < ((n : ℝ) / Real.exp 1) ^ n := pow_pos (div_pos hn0 he) n
  have hP2 : (0 : ℝ) < (((n : ℝ) / Real.exp 1) ^ n) ^ 2 := pow_pos hP 2
  -- rewrite both sides as single fractions
  have hLHS : (Nat.centralBinom n : ℝ) * Real.sqrt n * stirlingSeq n ^ 2
      = ((Nat.centralBinom n : ℝ) * Real.sqrt n * (n ! : ℝ) ^ 2)
          / (2 * (n : ℝ) * (((n : ℝ) / Real.exp 1) ^ n) ^ 2) := by
    rw [hval_n, div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hRHS : stirlingSeq (2 * n) * 4 ^ n
      = ((2 * n)! : ℝ) / (2 * Real.sqrt (n : ℝ) * (((n : ℝ) / Real.exp 1) ^ n) ^ 2) := by
    rw [hval_2n]
    have hPne : (((n : ℝ) / Real.exp 1) ^ n) ≠ 0 := hP.ne'
    have hP2ne : (((n : ℝ) / Real.exp 1) ^ n) ^ 2 ≠ 0 := hP2.ne'
    have h4ne : (4 : ℝ) ^ n ≠ 0 := by positivity
    have hqne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsn
    field_simp
  have hBne : (2 * (n : ℝ) * (((n : ℝ) / Real.exp 1) ^ n) ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hn0.ne') hP2.ne'
  have hDne : (2 * Real.sqrt (n : ℝ) * (((n : ℝ) / Real.exp 1) ^ n) ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hsn.ne') hP2.ne'
  rw [hLHS, hRHS, div_eq_div_iff hBne hDne]
  -- goal: (c·√n·(n !)²)·(2√n·P²) = (2n)!·(2n·P²)
  linear_combination
    (2 * (((n : ℝ) / Real.exp 1) ^ n) ^ 2 * Real.sqrt (n : ℝ) ^ 2) * hfac
    + (2 * (((n : ℝ) / Real.exp 1) ^ n) ^ 2 * ((2 * n)! : ℝ)) * Real.sq_sqrt hn0.le

/-!
## Part II: The explicit correction factor `ratioR`
-/

/-- The correction factor: the ratio of `betaDiag n` to its leading term. -/
noncomputable def ratioR (n : ℕ) : ℝ :=
  stirlingSeq n ^ 2 / (Real.sqrt π * stirlingSeq (2 * n))

/-- **The exact factored form.**  `betaDiag n = √(πn)/((2n+1)·4ⁿ) · ratioR n`. -/
theorem betaDiag_eq (n : ℕ) (hn : n ≠ 0) :
    betaDiag n = Real.sqrt (π * n) / ((2 * (n : ℝ) + 1) * 4 ^ n) * ratioR n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hsπ : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr hπ
  have hs2n : (0 : ℝ) < stirlingSeq (2 * n) :=
    lt_of_lt_of_le hsπ (Stirling.sqrt_pi_le_stirlingSeq (by omega))
  have hcb : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by
    have := Nat.centralBinom_pos n; exact_mod_cast this
  have hsplit : Real.sqrt (π * (n : ℝ)) = Real.sqrt π * Real.sqrt (n : ℝ) :=
    Real.sqrt_mul hπ.le _
  have hcru := centralBinom_stirlingSeq n hn
  have hD1ne : ((2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ)) ≠ 0 :=
    mul_ne_zero (by positivity) hcb.ne'
  have hD2ne : ((2 * (n : ℝ) + 1) * 4 ^ n * (Real.sqrt π * stirlingSeq (2 * n))) ≠ 0 :=
    mul_ne_zero (by positivity) (mul_ne_zero hsπ.ne' hs2n.ne')
  rw [betaDiag, ratioR, hsplit, div_mul_div_comm, div_eq_div_iff hD1ne hD2ne]
  -- goal: 1 * ((2n+1)·4ⁿ·(√π·S₂)) = (√π·√n·S²) · ((2n+1)·centralBinom)
  linear_combination (-(Real.sqrt π * (2 * (n : ℝ) + 1))) * hcru

/-!
## Part III: Effective two-sided bounds on `ratioR`

Mathlib gives `√π ≤ stirlingSeq n` (all `n ≥ 1`) and antitonicity gives the upper
value `stirlingSeq n ≤ stirlingSeq 1 = e/√2`.  Both plug into `ratioR`.
-/

/-- Upper bound for `stirlingSeq`: it never exceeds its first value `e/√2`. -/
theorem stirlingSeq_le (n : ℕ) (hn : n ≠ 0) : stirlingSeq n ≤ Real.exp 1 / Real.sqrt 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  simpa [Function.comp, Stirling.stirlingSeq_one] using h

/-- Lower envelope: `√(2π)/e ≤ ratioR n` for all `n ≥ 1`. -/
theorem ratioR_ge (n : ℕ) (hn : n ≠ 0) : Real.sqrt (2 * π) / Real.exp 1 ≤ ratioR n := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hsπ : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr hπ
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hlow_n : Real.sqrt π ≤ stirlingSeq n := Stirling.sqrt_pi_le_stirlingSeq hn
  have hlow_2n : Real.sqrt π ≤ stirlingSeq (2 * n) :=
    Stirling.sqrt_pi_le_stirlingSeq (by omega)
  have hup_2n : stirlingSeq (2 * n) ≤ Real.exp 1 / Real.sqrt 2 :=
    stirlingSeq_le (2 * n) (by omega)
  have hsn_pos : (0 : ℝ) < stirlingSeq n := lt_of_lt_of_le hsπ hlow_n
  -- numerator ≥ π, denominator ≤ √π·(e/√2)
  have hnum : π ≤ stirlingSeq n ^ 2 := by
    have := mul_le_mul hlow_n hlow_n hsπ.le hsn_pos.le
    rw [Real.mul_self_sqrt hπ.le] at this
    calc π = π := rfl
      _ ≤ stirlingSeq n * stirlingSeq n := this
      _ = stirlingSeq n ^ 2 := by ring
  have hden : Real.sqrt π * stirlingSeq (2 * n) ≤ Real.sqrt π * (Real.exp 1 / Real.sqrt 2) :=
    mul_le_mul_of_nonneg_left hup_2n hsπ.le
  have hden_pos : (0 : ℝ) < Real.sqrt π * stirlingSeq (2 * n) :=
    mul_pos hsπ (lt_of_lt_of_le hsπ hlow_2n)
  rw [ratioR, le_div_iff₀ hden_pos]
  calc Real.sqrt (2 * π) / Real.exp 1 * (Real.sqrt π * stirlingSeq (2 * n))
      ≤ Real.sqrt (2 * π) / Real.exp 1 * (Real.sqrt π * (Real.exp 1 / Real.sqrt 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hup_2n hsπ.le
    _ = π := by
        have h2 : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt hπ.le
        have he' : Real.exp 1 ≠ 0 := he.ne'
        have hs2' : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) π]
        field_simp
        linear_combination h2
    _ ≤ stirlingSeq n ^ 2 := hnum

/-- Upper envelope: `ratioR n ≤ e²/(2π)` for all `n ≥ 1`. -/
theorem ratioR_le (n : ℕ) (hn : n ≠ 0) : ratioR n ≤ Real.exp 1 ^ 2 / (2 * π) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hsπ : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr hπ
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hup_n : stirlingSeq n ≤ Real.exp 1 / Real.sqrt 2 := stirlingSeq_le n hn
  have hlow_2n : Real.sqrt π ≤ stirlingSeq (2 * n) :=
    Stirling.sqrt_pi_le_stirlingSeq (by omega)
  have hsn_pos : (0 : ℝ) < stirlingSeq n :=
    lt_of_lt_of_le hsπ (Stirling.sqrt_pi_le_stirlingSeq hn)
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- numerator ≤ e²/2, denominator ≥ √π·√π = π
  have hnum : stirlingSeq n ^ 2 ≤ Real.exp 1 ^ 2 / 2 := by
    have hup_nonneg : (0 : ℝ) ≤ Real.exp 1 / Real.sqrt 2 := by positivity
    have := mul_le_mul hup_n hup_n hsn_pos.le hup_nonneg
    calc stirlingSeq n ^ 2 = stirlingSeq n * stirlingSeq n := by ring
      _ ≤ (Real.exp 1 / Real.sqrt 2) * (Real.exp 1 / Real.sqrt 2) := this
      _ = Real.exp 1 ^ 2 / 2 := by
            rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring
  have hden : π ≤ Real.sqrt π * stirlingSeq (2 * n) := by
    have := mul_le_mul_of_nonneg_left hlow_2n hsπ.le
    rwa [Real.mul_self_sqrt hπ.le] at this
  have hden_pos : (0 : ℝ) < Real.sqrt π * stirlingSeq (2 * n) :=
    mul_pos hsπ (lt_of_lt_of_le hsπ hlow_2n)
  have hπ' : π ≠ 0 := hπ.ne'
  rw [ratioR, div_le_iff₀ hden_pos]
  calc stirlingSeq n ^ 2 ≤ Real.exp 1 ^ 2 / 2 := hnum
    _ = Real.exp 1 ^ 2 / (2 * π) * π := by field_simp
    _ ≤ Real.exp 1 ^ 2 / (2 * π) * (Real.sqrt π * stirlingSeq (2 * n)) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-!
## Part IV: The ratio tends to one (recovering the asymptotic)
-/

/-- `ratioR n → 1`, so `betaDiag_eq` recovers `betaDiag_isEquivalent`. -/
theorem ratioR_tendsto_one : Tendsto ratioR atTop (𝓝 1) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hsπ : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr hπ
  have hk : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have h1 : Tendsto (fun n : ℕ => stirlingSeq n) atTop (𝓝 (Real.sqrt π)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi
  have h2 : Tendsto (fun n : ℕ => stirlingSeq (2 * n)) atTop (𝓝 (Real.sqrt π)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp hk
  have hden_ne : Real.sqrt π * Real.sqrt π ≠ 0 := by positivity
  have hlim : Tendsto ratioR atTop
      (𝓝 (Real.sqrt π ^ 2 / (Real.sqrt π * Real.sqrt π))) :=
    (h1.pow 2).div (tendsto_const_nhds.mul h2) hden_ne
  have hval : Real.sqrt π ^ 2 / (Real.sqrt π * Real.sqrt π) = 1 := by
    rw [Real.sq_sqrt hπ.le, Real.mul_self_sqrt hπ.le, div_self hπ.ne']
  rwa [hval] at hlim

/-!
## Part V: The effective two-sided rate for `betaDiag`
-/

/-- **Effective lower bound.** `(√(2π)/e)·√(πn)/((2n+1)·4ⁿ) ≤ betaDiag n`, all `n ≥ 1`. -/
theorem betaDiag_lower (n : ℕ) (hn : n ≠ 0) :
    Real.sqrt (2 * π) / Real.exp 1 * (Real.sqrt (π * n) / ((2 * (n : ℝ) + 1) * 4 ^ n))
      ≤ betaDiag n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have htnn : (0 : ℝ) ≤ Real.sqrt (π * n) / ((2 * (n : ℝ) + 1) * 4 ^ n) := by positivity
  rw [betaDiag_eq n hn, mul_comm (Real.sqrt (2 * π) / Real.exp 1)]
  exact mul_le_mul_of_nonneg_left (ratioR_ge n hn) htnn

/-- **Effective upper bound.** `betaDiag n ≤ (e²/(2π))·√(πn)/((2n+1)·4ⁿ)`, all `n ≥ 1`. -/
theorem betaDiag_upper (n : ℕ) (hn : n ≠ 0) :
    betaDiag n
      ≤ Real.exp 1 ^ 2 / (2 * π) * (Real.sqrt (π * n) / ((2 * (n : ℝ) + 1) * 4 ^ n)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have htnn : (0 : ℝ) ≤ Real.sqrt (π * n) / ((2 * (n : ℝ) + 1) * 4 ^ n) := by positivity
  rw [betaDiag_eq n hn, mul_comm (Real.exp 1 ^ 2 / (2 * π))]
  exact mul_le_mul_of_nonneg_left (ratioR_le n hn) htnn

end BetaDiagEffectiveRate
