import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
- [ ] Full continuous Stirling (stated, needs Laplace method)

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
  sorry

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
-- require ~500 lines of integral analysis. We state it as a theorem
-- with sorry, making it a candidate for Aristotle proof search.

/-- **Continuous Stirling for Gamma** (stated):
    For x → +∞, Γ(x+1) is asymptotically equivalent to √(2πx)·(x/e)^x.

    This is the real-variable generalization of the factorial Stirling formula.
    The proof requires the Laplace method for asymptotic evaluation of integrals. -/
theorem gamma_continuous_stirling :
    Tendsto (fun x : ℝ => Real.Gamma (x + 1) / (Real.sqrt (2 * π * x) * (x / Real.exp 1) ^ x))
      atTop (nhds 1) := by
  sorry

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
-- Summary and Exports
-- ============================================================

-- Main results:
#check @gamma_eq_factorial        -- Γ(n+1) = n!
#check @gamma_isEquivalent_stirling -- Γ(n+1) ~ √(2πn)·(n/e)^n
#check @gamma_lower_bound         -- √(2πn)·(n/e)^n ≤ Γ(n+1)
#check @gamma_div_stirling_tendsto_one -- Γ(n+1)/approx → 1
#check @log_gamma_lower_bound     -- Log-Gamma lower bound
#check @gamma_one_half            -- Γ(1/2) = √π
#check @gamma_stirling_relative_error_tendsto -- Error → 0

end StirlingGamma
