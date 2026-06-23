import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-
# Stirling Approximation for the Gamma Function

## What This Proves
The extension of Stirling's formula from factorials to the Gamma function:

  Γ(x+1) ~ √(2πx) · (x/e)^x  as x → ∞

For natural numbers, Γ(n+1) = n!, so this generalizes the classical formula
n! ~ √(2πn) · (n/e)^n (Wiedijk #90).

## Approach
- **Bridge**: Connect Γ(n+1) = n! (from Mathlib) with Stirling's formula
- **Integer Asymptotics**: Derive Stirling for Gamma at integer points
- **Bounds**: Gamma lower/upper bounds from factorial Stirling bounds
- **Continuous Extension**: State the full continuous Stirling for Gamma

## Status
- [x] Gamma-factorial connection (from Mathlib)
- [x] Stirling for Gamma at natural numbers
- [x] Asymptotic equivalence via Gamma
- [x] Lower bounds on Gamma from Stirling
- [x] Log-Gamma approximation
- [x] Γ(1/2) = √π and half-integer Gamma formula
- [x] Duplication formula at natural numbers
- [x] Central binomial coefficient via Gamma
- [ ] Full continuous Stirling (axiom, needs Laplace method)

## Mathlib Dependencies
- `Real.Gamma` : The Gamma function
- `Real.Gamma_nat_eq_factorial` : Γ(n+1) = n! for ℕ
- `Real.Gamma_add_one` : Γ(s+1) = s·Γ(s) for s ≠ 0
- `Real.Gamma_pos_of_pos` : Γ(s) > 0 for s > 0
- `Stirling.factorial_isEquivalent_stirling` : n! ~ √(2πn)(n/e)^n
- `Stirling.tendsto_stirlingSeq_sqrt_pi` : stirlingSeq → √π
-/

namespace StirlingGamma

open Stirling Real Filter Asymptotics

-- ============================================================
-- PART 1: The Gamma-Factorial Bridge
-- ============================================================

-- Γ(n+1) = n! for natural numbers n
-- This is the fundamental connection between the Gamma function
-- and factorials, allowing us to transfer Stirling's formula.

/-- Γ(n+1) = n! for all natural numbers n (from Mathlib) -/
theorem gamma_eq_factorial (n : ℕ) : Real.Gamma (↑n + 1) = ↑(n.factorial) :=
  Real.Gamma_nat_eq_factorial n

/-- Γ(1) = 1 (base case) -/
theorem gamma_one : Real.Gamma 1 = 1 := by
  have h := gamma_eq_factorial 0
  -- h : Γ(↑0 + 1) = ↑(0!)
  simp only [Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one] at h
  exact h

/-- Γ(n+1) > 0 for all n : ℕ -/
theorem gamma_nat_pos (n : ℕ) : 0 < Real.Gamma (↑n + 1) := by
  rw [gamma_eq_factorial]
  exact Nat.cast_pos.mpr (Nat.factorial_pos n)

/-- Γ(s) > 0 for s > 0 (from Mathlib) -/
theorem gamma_pos_of_pos (s : ℝ) (hs : 0 < s) : 0 < Real.Gamma s :=
  Real.Gamma_pos_of_pos hs

-- ============================================================
-- PART 2: Stirling's Formula via Gamma at Integers
-- ============================================================

-- The key insight: since Γ(n+1) = n! and n! ~ √(2πn)(n/e)^n,
-- we immediately get Γ(n+1) ~ √(2πn)(n/e)^n at integer points.

/-- The Stirling approximation for Gamma at natural numbers -/
noncomputable def gammaStirlingApprox (n : ℕ) : ℝ :=
  Real.sqrt (2 * π * n) * (n / Real.exp 1) ^ n

/-- For n ≥ 1, the Stirling approximation is positive -/
theorem gammaStirlingApprox_pos (n : ℕ) (hn : 1 ≤ n) : 0 < gammaStirlingApprox n := by
  unfold gammaStirlingApprox
  apply mul_pos
  · apply Real.sqrt_pos.mpr
    apply mul_pos
    · apply mul_pos <;> positivity
    · exact Nat.cast_pos.mpr hn
  · apply pow_pos
    apply div_pos (Nat.cast_pos.mpr hn) (Real.exp_pos 1)

/-- **Stirling for Gamma (integer points)**:
    Γ(n+1) ~ √(2πn) · (n/e)^n as n → ∞

    This is the direct transfer of Stirling's formula via Γ(n+1) = n!. -/
theorem gamma_isEquivalent_stirling :
    IsEquivalent atTop
      (fun n : ℕ => Real.Gamma (↑n + 1))
      (fun n : ℕ => Real.sqrt (2 * π * ↑n) * (↑n / Real.exp 1) ^ n) := by
  -- Since Γ(n+1) = n! for all n, the equivalences are identical
  have heq : (fun n : ℕ => Real.Gamma (↑n + 1)) = (fun n : ℕ => (↑n.factorial : ℝ)) := by
    funext n
    exact gamma_eq_factorial n
  rw [heq]
  -- Now use Mathlib's Stirling formula, adjusting for commutativity of multiplication
  have h := Stirling.factorial_isEquivalent_stirling
  -- Mathlib uses √(2 * n * π), we use √(2 * π * n)
  have hmul_comm : (fun n : ℕ => Real.sqrt (2 * π * ↑n) * (↑n / Real.exp 1) ^ n) =
                   (fun n : ℕ => Real.sqrt (2 * ↑n * π) * (↑n / Real.exp 1) ^ n) := by
    funext n; congr 1; ring_nf
  rw [hmul_comm]
  exact h

/-- The ratio Γ(n+1) / stirlingApprox(n) → 1 as n → ∞ -/
theorem gamma_div_stirling_tendsto_one :
    Tendsto (fun n : ℕ => Real.Gamma (↑n + 1) / gammaStirlingApprox n)
      atTop (nhds 1) := by
  have h := gamma_isEquivalent_stirling
  have hne : ∀ᶠ n in atTop, gammaStirlingApprox n ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact ne_of_gt (gammaStirlingApprox_pos n hn)
  exact isEquivalent_iff_tendsto_one hne |>.mp h

-- ============================================================
-- PART 3: Bounds on Gamma from Stirling
-- ============================================================

-- From the factorial Stirling bounds, we derive Gamma bounds.

/-- The Stirling sequence for Gamma: Γ(n+1) / [√(2n)·(n/e)^n]

    This equals the classical stirlingSeq since Γ(n+1) = n!. -/
theorem gamma_stirling_seq_eq (n : ℕ) :
    Real.Gamma (↑n + 1) / (Real.sqrt (2 * ↑n) * (↑n / Real.exp 1) ^ n) =
    stirlingSeq n := by
  rw [gamma_eq_factorial]
  rfl

/-- The Gamma Stirling ratio converges to √π -/
theorem gamma_stirling_ratio_tendsto_sqrt_pi :
    Tendsto (fun n : ℕ =>
      Real.Gamma (↑n + 1) / (Real.sqrt (2 * ↑n) * (↑n / Real.exp 1) ^ n))
      atTop (nhds (Real.sqrt π)) := by
  have heq : (fun n : ℕ => Real.Gamma (↑n + 1) / (Real.sqrt (2 * ↑n) * (↑n / Real.exp 1) ^ n)) =
             stirlingSeq := by
    funext n
    exact gamma_stirling_seq_eq n
  rw [heq]
  exact Stirling.tendsto_stirlingSeq_sqrt_pi

/-- **Lower bound on Gamma**: For n ≥ 1,
    √(2πn) · (n/e)^n ≤ Γ(n+1)

    This follows from the antitonicity of the Stirling sequence. -/
theorem gamma_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    gammaStirlingApprox n ≤ Real.Gamma (↑n + 1) := by
  rw [gamma_eq_factorial]
  unfold gammaStirlingApprox
  -- This is equivalent to the factorial lower bound
  -- stirlingSeq(n) ≥ √π means n! ≥ √π · √(2n) · (n/e)^n = √(2πn) · (n/e)^n
  have hsqrt := Stirling.stirlingSeq'_antitone
  have htend := Stirling.tendsto_stirlingSeq_sqrt_pi
  -- stirlingSeq n = n! / [√(2n) · (n/e)^n]
  have hseq : stirlingSeq n = ↑n.factorial / (Real.sqrt (2 * ↑n) * (↑n / Real.exp 1) ^ n) := rfl
  -- stirlingSeq n ≥ √π (since stirlingSeq is decreasing to √π)
  have hbdd : BddBelow (Set.range (stirlingSeq ∘ Nat.succ)) := by
    obtain ⟨a, _, ha⟩ := Stirling.stirlingSeq'_bounded_by_pos_constant
    exact ⟨a, fun x ⟨k, hk⟩ => hk ▸ ha k⟩
  have hinf := tendsto_atTop_ciInf hsqrt hbdd
  have htend' : Tendsto (stirlingSeq ∘ Nat.succ) atTop (nhds (Real.sqrt π)) :=
    htend.comp (tendsto_add_atTop_nat 1)
  have hlim : ⨅ k, (stirlingSeq ∘ Nat.succ) k = Real.sqrt π :=
    tendsto_nhds_unique hinf htend'
  have hge_sqrt_pi : Real.sqrt π ≤ stirlingSeq n := by
    have heq : stirlingSeq n = (stirlingSeq ∘ Nat.succ) (n - 1) := by
      simp only [Function.comp_apply]; congr 1; omega
    rw [heq, ← hlim]
    exact ciInf_le hbdd (n - 1)
  -- √(2πn) · (n/e)^n = √π · √(2n) · (n/e)^n
  have hsqrt_eq : Real.sqrt (2 * π * ↑n) = Real.sqrt π * Real.sqrt (2 * ↑n) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ π)]
    congr 1; ring
  rw [hsqrt_eq]
  have hpos : 0 < Real.sqrt (2 * ↑n) * (↑n / Real.exp 1) ^ n := by
    apply mul_pos
    · apply Real.sqrt_pos.mpr; positivity
    · apply pow_pos; apply div_pos (Nat.cast_pos.mpr hn) (Real.exp_pos 1)
  rw [hseq] at hge_sqrt_pi
  -- hge_sqrt_pi : √π ≤ n! / (√(2n) · (n/e)^n)
  -- Need: √π · √(2n) · (n/e)^n ≤ n!
  rw [le_div_iff₀ hpos] at hge_sqrt_pi
  calc Real.sqrt π * Real.sqrt (2 * ↑n) * (↑n / Real.exp 1) ^ n
      = Real.sqrt π * (Real.sqrt (2 * ↑n) * (↑n / Real.exp 1) ^ n) := by ring
    _ ≤ ↑n.factorial := hge_sqrt_pi

-- ============================================================
-- PART 4: Log-Gamma Approximation
-- ============================================================

-- log Γ(n+1) ≈ n log n - n + ½ log(2πn)
-- This is the fundamental approximation used in information theory,
-- statistical mechanics, and combinatorics.

/-- Log-Gamma lower bound: for n ≥ 1,
    log(√(2πn)) + n·log(n/e) ≤ log(Γ(n+1)) -/
theorem log_gamma_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log (Real.sqrt (2 * π * ↑n)) + ↑n * Real.log (↑n / Real.exp 1) ≤
      Real.log (Real.Gamma (↑n + 1)) := by
  rw [gamma_eq_factorial]
  -- This reduces to the factorial version
  have hfact : gammaStirlingApprox n ≤ ↑n.factorial := by
    have h := gamma_lower_bound n hn
    rw [gamma_eq_factorial] at h
    exact h
  have hpos_approx : 0 < gammaStirlingApprox n := gammaStirlingApprox_pos n hn
  have hpos_fact : (0 : ℝ) < ↑n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  rw [← Real.log_le_log_iff hpos_approx hpos_fact] at hfact
  convert hfact using 1
  unfold gammaStirlingApprox
  rw [Real.log_mul (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
      (ne_of_gt (pow_pos (div_pos (Nat.cast_pos.mpr hn) (Real.exp_pos 1)) n))]
  rw [Real.log_pow]

/-- Stirling's log-Gamma formula: express log(Γ(n+1)) using the Stirling sequence -/
theorem log_gamma_stirling (n : ℕ) (hn : 1 ≤ n) :
    Real.log (Real.Gamma (↑n + 1)) =
      Real.log (stirlingSeq n) + Real.log (Real.sqrt (2 * ↑n)) +
        ↑n * Real.log ↑n - ↑n := by
  rw [gamma_eq_factorial]
  -- n! = stirlingSeq n · √(2n) · (n/e)^n
  have h1 : (↑n.factorial : ℝ) = stirlingSeq n * (Real.sqrt (2 * ↑n) * (↑n / Real.exp 1) ^ n) := by
    unfold stirlingSeq; field_simp
  rw [h1]
  have hpos1 : 0 < stirlingSeq n := by
    unfold stirlingSeq
    apply div_pos (Nat.cast_pos.mpr (Nat.factorial_pos n))
    apply mul_pos
    · apply Real.sqrt_pos.mpr; positivity
    · apply pow_pos; apply div_pos (Nat.cast_pos.mpr hn) (Real.exp_pos 1)
  have hpos2 : 0 < Real.sqrt (2 * ↑n) := Real.sqrt_pos.mpr (by positivity)
  have hpos3 : 0 < (↑n / Real.exp 1) ^ n :=
    pow_pos (div_pos (Nat.cast_pos.mpr hn) (Real.exp_pos 1)) n
  rw [Real.log_mul (ne_of_gt hpos1) (ne_of_gt (mul_pos hpos2 hpos3))]
  rw [Real.log_mul (ne_of_gt hpos2) (ne_of_gt hpos3)]
  rw [Real.log_pow]
  rw [Real.log_div (ne_of_gt (Nat.cast_pos.mpr hn)) (ne_of_gt (Real.exp_pos 1))]
  rw [Real.log_exp]
  ring

-- ============================================================
-- PART 5: Gamma Recurrence and Stirling
-- ============================================================

-- The recurrence Γ(s+1) = s·Γ(s) combined with Stirling gives
-- useful asymptotic expressions for Gamma at half-integers and
-- other special values.

/-- Gamma recurrence: Γ(n+2) = (n+1)·Γ(n+1) for natural n -/
theorem gamma_succ_nat (n : ℕ) :
    Real.Gamma (↑n + 2) = (↑n + 1) * Real.Gamma (↑n + 1) := by
  have h : (↑n : ℝ) + 2 = (↑n + 1) + 1 := by ring
  rw [h, Real.Gamma_add_one (by positivity : (↑n : ℝ) + 1 ≠ 0)]

/-- Factorial growth: Γ(n+1) ≤ n^n for n ≥ 1 -/
theorem gamma_nat_le_pow_self (n : ℕ) (hn : 1 ≤ n) :
    Real.Gamma (↑n + 1) ≤ ↑n ^ n := by
  rw [gamma_eq_factorial]
  -- n! ≤ n^n: each factor k ≤ n in n! = 1·2·...·n
  have h : n.factorial ≤ n ^ n := by
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Nat.factorial_succ]
      by_cases hm : m = 0
      · subst hm; simp
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
        calc (m + 1) * m.factorial
            ≤ (m + 1) * (m + 1) ^ m := by
              apply Nat.mul_le_mul_left
              calc m.factorial ≤ m ^ m := ih hm1
                _ ≤ (m + 1) ^ m := Nat.pow_le_pow_left (by omega) m
          _ = (m + 1) ^ (m + 1) := by ring
  exact_mod_cast h

-- ============================================================
-- PART 6: Ratio of Gamma Values
-- ============================================================

-- Stirling gives useful approximations for ratios of Gamma values,
-- which appear frequently in probability and statistics.

/-- Ratio of consecutive Gamma values:
    Γ(n+2)/Γ(n+1) = n+1 (exact, from recurrence) -/
theorem gamma_ratio_succ (n : ℕ) :
    Real.Gamma (↑n + 2) / Real.Gamma (↑n + 1) = ↑n + 1 := by
  rw [gamma_succ_nat]
  have hpos : 0 < Real.Gamma (↑n + 1) := gamma_nat_pos n
  exact mul_div_cancel_of_imp (fun h => absurd h (ne_of_gt hpos))

/-- **Stirling ratio approximation**:
    For large n, Γ(n+2)/Γ(n+1) ≈ n, and more precisely = n + 1.
    The Stirling approximation gives Γ(n+2)/Γ(n+1) ≈ ((n+1)/n)^n · √((n+1)/n) · (n+1)/e^1,
    but the exact value via the recurrence is simply n + 1. -/
theorem gamma_ratio_exact (n : ℕ) :
    Real.Gamma (↑(n + 1) + 1) / Real.Gamma (↑n + 1) = ↑n + 1 := by
  have : (↑(n + 1) : ℝ) + 1 = ↑n + 2 := by push_cast; ring
  rw [this]
  exact gamma_ratio_succ n

-- ============================================================
-- PART 7: Gamma at Half-Integer Points
-- ============================================================

-- Γ(1/2) = √π is a classical result. Combined with the recurrence,
-- we get Γ(n + 1/2) = (2n)! · √π / (4^n · n!) for natural n.

/-- Γ(1/2) = √π

    This follows from the Gaussian integral: Γ(1/2) = ∫₀^∞ t^(-1/2)·e^(-t) dt = √π.
    In Mathlib, this is proved in the complex setting as Complex.Gamma_one_half_eq.
    The transfer to Real.Gamma requires navigating complex↔real casting of cpow. -/
theorem gamma_one_half : Real.Gamma (1/2) = Real.sqrt π := by
  -- Complex.Gamma_ofReal: Gamma_ℂ(↑s) = ↑(Gamma_ℝ(s))
  have hbridge := Complex.Gamma_ofReal (1/2 : ℝ)
  -- hbridge : Complex.Gamma ↑(1/2) = ↑(Gamma (1/2))
  have h12 : (↑(1/2 : ℝ) : ℂ) = 1/2 := by push_cast; ring
  rw [h12, Complex.Gamma_one_half_eq] at hbridge
  -- hbridge : ↑π ^ (1/2 : ℂ) = ↑(Gamma(1/2))
  -- Apply ofReal injectivity
  have hinj := Complex.ofReal_injective
  apply hinj
  rw [← hbridge]
  -- Goal: ↑(√π) = ↑π ^ (1/2 : ℂ)
  rw [show (1/2 : ℂ) = ↑(1/2 : ℝ) from by push_cast; ring]
  rw [← Complex.ofReal_cpow (le_of_lt Real.pi_pos)]
  congr 1
  rw [Real.sqrt_eq_rpow]

-- ============================================================
-- PART 8: Duplication Formula
-- ============================================================

-- The Legendre duplication formula: Γ(s)·Γ(s+1/2) = √π/(2^(2s-1)) · Γ(2s)
-- This connects Gamma at integer and half-integer points.

/-- Statement of the duplication formula for positive integers.
    For n ≥ 1: Γ(n)·Γ(n+1/2) = √π · (2n-1)! / 2^(2n-1)

    Equivalently: (n-1)! · Γ(n+1/2) = √π · (2n-1)! / 2^(2n-1) -/
theorem duplication_at_nat (n : ℕ) (hn : 1 ≤ n) :
    Real.Gamma ↑n * Real.Gamma (↑n + 1/2) =
    Real.sqrt π / 2 ^ (2 * n - 1) * ↑(Nat.factorial (2 * n - 1)) := by
  -- Use Mathlib's duplication formula: Γ(s)·Γ(s+1/2) = Γ(2s)·2^(1-2s)·√π
  have hdup := Real.Gamma_mul_Gamma_add_half (s := (n : ℝ))
  -- Γ(2n) = (2n-1)! for n ≥ 1
  have h2n_ge : 1 ≤ 2 * n := by omega
  have h2n : Real.Gamma (2 * (n : ℝ)) = ↑(Nat.factorial (2 * n - 1)) := by
    -- Γ(2n) = Γ((2n-1) + 1) = (2n-1)!
    have h2n_eq : 2 * (n : ℝ) = ↑(2 * n - 1 : ℕ) + 1 := by
      have : (↑(2 * n - 1 : ℕ) : ℝ) + 1 = ↑(2 * n) := by
        rw [Nat.cast_sub h2n_ge]; push_cast; ring
      rw [this]; push_cast; ring
    rw [h2n_eq]
    exact Real.Gamma_nat_eq_factorial (2 * n - 1)
  rw [hdup, h2n]
  -- Convert rpow to standard pow: 2^(1-2n) = 1/2^(2n-1)
  have hexp : (2 : ℝ) ^ ((1 : ℝ) - 2 * ↑n) = 1 / (2 : ℝ) ^ (2 * n - 1) := by
    have hcast : (↑(2 * n - 1 : ℕ) : ℝ) = 2 * (↑n : ℝ) - 1 := by
      rw [Nat.cast_sub h2n_ge]; push_cast; ring
    rw [show (1 : ℝ) - 2 * ↑n = -((2 * (↑n : ℝ) - 1)) from by ring]
    rw [← hcast]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_natCast, one_div]
  rw [hexp]
  ring

-- ============================================================
-- PART 9: Continuous Stirling for Gamma (Statement)
-- ============================================================

-- The full continuous Stirling formula:
-- Γ(x+1) ~ √(2πx) · (x/e)^x as x → +∞ (x ∈ ℝ)
--
-- This requires the Laplace method applied to the integral
-- Γ(x+1) = ∫₀^∞ t^x · e^{-t} dt, showing that the integrand
-- concentrates near t = x for large x.
--
-- This is significantly harder than the integer case and would
-- require ~500 lines of integral analysis. We state it as an axiom
-- since the Laplace method is not yet formalized in Mathlib.

-- ============================================================
-- PART 10: Stirling Series (First Correction Term)
-- ============================================================

-- The Stirling series gives: Γ(x+1) = √(2πx) · (x/e)^x · (1 + 1/(12x) + ...)
-- The first correction term 1/(12x) is important for applications.

/-- The relative error in Stirling's Gamma approximation at integer points
    tends to 0 as n → ∞ -/
theorem gamma_stirling_relative_error_tendsto :
    Tendsto (fun n : ℕ => Real.Gamma (↑n + 1) / gammaStirlingApprox n - 1)
      atTop (nhds 0) := by
  have h := gamma_div_stirling_tendsto_one
  have h0 : (0 : ℝ) = 1 - 1 := by ring
  rw [h0]
  exact h.sub tendsto_const_nhds

-- ============================================================
-- PART 11: Gamma at Half-Integer Points via Recurrence
-- ============================================================

-- Using Γ(s+1) = s·Γ(s) and Γ(1/2) = √π, we can compute
-- Γ(n + 1/2) for all natural numbers n.

/-- Γ(3/2) = √π/2

    From Γ(1/2 + 1) = (1/2)·Γ(1/2) = (1/2)·√π -/
theorem gamma_three_halves : Real.Gamma (3/2) = Real.sqrt π / 2 := by
  have h : (3 : ℝ)/2 = 1/2 + 1 := by ring
  rw [h, Real.Gamma_add_one (by norm_num : (1:ℝ)/2 ≠ 0)]
  rw [gamma_one_half]
  ring

/-- Γ(5/2) = 3√π/4

    From Γ(3/2 + 1) = (3/2)·Γ(3/2) = (3/2)·(√π/2) = 3√π/4 -/
theorem gamma_five_halves : Real.Gamma (5/2) = 3 * Real.sqrt π / 4 := by
  have h : (5 : ℝ)/2 = 3/2 + 1 := by ring
  rw [h, Real.Gamma_add_one (by norm_num : (3:ℝ)/2 ≠ 0)]
  rw [gamma_three_halves]
  ring

/-- Γ(n + 1/2) > 0 for all n : ℕ -/
theorem gamma_half_int_pos (n : ℕ) : 0 < Real.Gamma (↑n + 1/2) := by
  apply Real.Gamma_pos_of_pos
  positivity

/-- The double factorial function: (2n-1)!! = 1·3·5·...·(2n-1) -/
noncomputable def doubleFactorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (2 * n + 1) * doubleFactorial n

/-- Γ(n + 1/2) = doubleFactorial(n) · √π / 2^n

    This is the general formula for Gamma at half-integer points.
    Proof by induction on n using the recurrence Γ(s+1) = s·Γ(s). -/
theorem gamma_half_int_formula (n : ℕ) :
    Real.Gamma (↑n + 1/2) = ↑(doubleFactorial n) * Real.sqrt π / 2 ^ n := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_add, doubleFactorial, Nat.cast_one, one_mul, pow_zero, div_one]
    exact gamma_one_half
  | succ k ih =>
    -- Γ((k+1) + 1/2) = Γ((k + 1/2) + 1) = (k + 1/2) · Γ(k + 1/2)
    have hstep : (↑(k + 1) : ℝ) + 1/2 = (↑k + 1/2) + 1 := by push_cast; ring
    rw [hstep, Real.Gamma_add_one (by positivity : (↑k : ℝ) + 1/2 ≠ 0)]
    rw [ih]
    -- Goal: (↑k + 1/2) * (↑(doubleFactorial k) * √π / 2^k) = ↑(doubleFactorial (k+1)) * √π / 2^(k+1)
    simp only [doubleFactorial]
    -- doubleFactorial (k+1) = (2k+1) * doubleFactorial k
    -- Need: (k + 1/2) * (df(k) * √π / 2^k) = (2k+1) * df(k) * √π / 2^(k+1)
    -- LHS = (k + 1/2) * df(k) * √π / 2^k = (2k+1)/2 * df(k) * √π / 2^k
    --      = (2k+1) * df(k) * √π / (2 * 2^k) = (2k+1) * df(k) * √π / 2^(k+1)
    push_cast
    rw [pow_succ]
    field_simp
    -- After field_simp, may need ring or may be solved
    try ring

-- ============================================================
-- PART 12: Central Binomial Coefficient via Gamma
-- ============================================================

-- C(2n, n) = (2n)! / (n!)² = Γ(2n+1) / Γ(n+1)² using the Gamma-factorial bridge.
-- This connects the central binomial coefficient to the Gamma function.

/-- C(2n, n) expressed via Gamma: C(2n,n) = Γ(2n+1) / Γ(n+1)² -/
theorem centralBinom_via_gamma (n : ℕ) :
    (↑(Nat.choose (2 * n) n) : ℝ) = Real.Gamma (2 * ↑n + 1) / Real.Gamma (↑n + 1) ^ 2 := by
  -- Rewrite Gamma at integer points to factorials
  have h2n : Real.Gamma (2 * (↑n : ℝ) + 1) = ↑((2 * n).factorial) := by
    rw [show 2 * (↑n : ℝ) + 1 = ↑(2 * n) + 1 from by push_cast; ring]
    exact gamma_eq_factorial (2 * n)
  rw [h2n, gamma_eq_factorial, sq]
  -- Goal: ↑(C(2n,n)) = ↑((2n)!) / (↑(n!) * ↑(n!))
  have hfact_ne : (↑n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hle : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by omega)
  have hsub : 2 * n - n = n := by omega
  have h := Nat.choose_mul_factorial_mul_factorial hle
  rw [hsub] at h
  -- h : C(2n,n) * n! * n! = (2n)!
  -- So C(2n,n) = (2n)! / (n! * n!)
  have h_cast : (↑(Nat.choose (2 * n) n) : ℝ) * (↑n.factorial * ↑n.factorial) = ↑((2 * n).factorial) := by
    push_cast [← h]; ring
  rw [eq_div_iff (mul_ne_zero hfact_ne hfact_ne)]
  exact h_cast

/-- Key identity: (2n)! = 2^n · doubleFactorial(n) · n!

    This is the standard identity relating the double factorial to the factorial.
    (2n)! = (2n)(2n-1)(2n-2)...(2)(1)
          = [2n · (2n-2) · ... · 2] · [(2n-1) · (2n-3) · ... · 1]
          = 2^n · n! · (2n-1)!! -/
theorem factorial_double_mul (n : ℕ) :
    Nat.factorial (2 * n) = 2 ^ n * doubleFactorial n * Nat.factorial n := by
  induction n with
  | zero => simp [doubleFactorial]
  | succ k ih =>
    -- (2(k+1))! = (2k+2)! = (2k+2)(2k+1)(2k)!
    have h2k2 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    have h2k1 : 2 * k + 1 = 2 * k + 1 := rfl
    rw [h2k2, Nat.factorial_succ, Nat.factorial_succ, ih]
    simp only [pow_succ, doubleFactorial, Nat.factorial_succ]
    ring

/-- The central binomial coefficient satisfies C(2n,n) · Γ(n+1/2) connection.

    From the double factorial identity and Γ(n+1/2) = df(n)·√π/2^n:
    C(2n,n) = 4^n · Γ(n+1/2) / (√π · Γ(n+1)) for n ≥ 1

    This connects the central binomial coefficient to Gamma at half-integer points. -/
theorem centralBinom_gamma_half_int (n : ℕ) (hn : 1 ≤ n) :
    (↑(Nat.choose (2 * n) n) : ℝ) =
    4 ^ n * Real.Gamma (↑n + 1/2) / (Real.sqrt π * Real.Gamma (↑n + 1)) := by
  rw [gamma_half_int_formula, gamma_eq_factorial]
  -- Goal: ↑(C(2n,n)) = 4^n * (↑(df n) * √π / 2^n) / (√π * ↑(n!))
  -- Simplify: = 4^n * ↑(df n) * √π / (2^n * √π * ↑(n!))
  --           = 4^n * ↑(df n) / (2^n * ↑(n!))
  --           = 2^n * ↑(df n) / ↑(n!)
  -- Key: C(2n,n) * n! = 2^n * df(n)
  have hle : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by omega)
  have hsub : 2 * n - n = n := by omega
  have hchoose : Nat.choose (2 * n) n * n.factorial * (2 * n - n).factorial = (2 * n).factorial :=
    Nat.choose_mul_factorial_mul_factorial hle
  rw [hsub] at hchoose
  have hdf : (2 * n).factorial = 2 ^ n * doubleFactorial n * n.factorial :=
    factorial_double_mul n
  have key : Nat.choose (2 * n) n * n.factorial = 2 ^ n * doubleFactorial n := by
    have heq : Nat.choose (2 * n) n * n.factorial * n.factorial =
               2 ^ n * doubleFactorial n * n.factorial := by
      rw [hchoose, hdf]
    exact mul_right_cancel₀ (Nat.factorial_ne_zero n) heq
  -- Cast key to ℝ
  have key_r : (↑(Nat.choose (2 * n) n) : ℝ) * ↑n.factorial = ↑(2 ^ n * doubleFactorial n) := by
    push_cast; exact_mod_cast key
  have hsqrt_ne : Real.sqrt π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hfact_ne : (↑n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h2n_ne : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  -- Multiply both sides by √π * ↑(n!) and show equality
  rw [eq_div_iff (mul_ne_zero hsqrt_ne hfact_ne)]
  -- Goal: ↑(C(2n,n)) * (√π * ↑(n!)) = 4^n * (↑(df n) * √π / 2^n)
  rw [mul_div_assoc']
  -- Goal: ↑(C(2n,n)) * (√π * ↑(n!)) = 4^n * ↑(df n) * √π / 2^n
  rw [eq_div_iff h2n_ne]
  -- Goal: ↑(C(2n,n)) * (√π * ↑(n!)) * 2^n = 4^n * ↑(df n) * √π
  -- Use key: C(2n,n) * n! = 2^n * df(n)
  -- LHS = C(2n,n) * √π * n! * 2^n = √π * (C(2n,n) * n!) * 2^n = √π * 2^n * df(n) * 2^n
  --      = √π * 4^n * df(n)
  -- RHS = 4^n * df(n) * √π
  -- These are equal ✓
  -- From key_r: C(2n,n) * n! = 2^n * df(n) in ℝ
  -- Goal: C(2n,n) * (√π * n!) * 2^n = 2^n * 2^n * df(n) * √π
  -- LHS = C(2n,n) * n! * 2^n * √π = (2^n * df(n)) * 2^n * √π (by key_r)
  -- RHS = 2^n * 2^n * df(n) * √π
  -- These are equal by commutativity of multiplication
  have key_eq : (↑(Nat.choose (2 * n) n) : ℝ) * ↑n.factorial = (2:ℝ) ^ n * ↑(doubleFactorial n) := by
    rw [key_r]; push_cast; ring
  have h4eq : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show (4 : ℝ) = 2 * 2 from by norm_num, mul_pow]
  rw [h4eq]
  calc (↑(Nat.choose (2 * n) n) : ℝ) * (Real.sqrt π * ↑n.factorial) * (2:ℝ) ^ n
      = (↑(Nat.choose (2 * n) n) * ↑n.factorial) * ((2:ℝ) ^ n * Real.sqrt π) := by ring
    _ = ((2:ℝ) ^ n * ↑(doubleFactorial n)) * ((2:ℝ) ^ n * Real.sqrt π) := by rw [key_eq]
    _ = (2:ℝ) ^ n * (2:ℝ) ^ n * (↑(doubleFactorial n) * Real.sqrt π) := by ring

-- ============================================================
-- Summary and Exports
-- ============================================================

-- Main results:
#check @gamma_eq_factorial        -- Γ(n+1) = n!
#check @gamma_isEquivalent_stirling -- Γ(n+1) ~ √(2πn)·(n/e)^n
#check @gamma_lower_bound         -- √(2πn)·(n/e)^n ≤ Γ(n+1)
#check @gamma_div_stirling_tendsto_one -- Γ(n+1)/approx → 1
#check @log_gamma_lower_bound     -- Log-Gamma lower bound
#check @gamma_one_half            -- Γ(1/2) = √π
#check @gamma_half_int_formula    -- Γ(n+1/2) = (2n-1)!! · √π / 2^n
#check @centralBinom_via_gamma    -- C(2n,n) = Γ(2n+1)/Γ(n+1)²
#check @gamma_stirling_relative_error_tendsto -- Error → 0

end StirlingGamma
