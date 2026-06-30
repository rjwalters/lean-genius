import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-
# The Continuous Stirling Formula for the Gamma Function

## What This Proves
The full **continuous** Stirling asymptotic for the real Gamma function:

  Γ(x+1) ~ √(2πx) · (x/e)^x   as  x → ∞   (x ∈ ℝ),

together with its logarithmic form

  log Γ(x+1) − (½·log(2πx) + x·log x − x) → 0.

The sibling entry `stirling-formula-oq-02` (StirlingFormulaOQ02.lean) established the
Stirling formula for Γ only at **integer** points (via Γ(n+1) = n!), and explicitly
left the continuous real-variable statement as an open question, noting it "requires
the Laplace method (~500 lines of integral analysis not yet in Mathlib)".

## Key Insight — no Laplace method needed
The continuous formula follows from **two ingredients already in Mathlib**:

  1. the discrete Stirling formula `Stirling.factorial_isEquivalent_stirling`, and
  2. **log-convexity of Γ** (`Real.convexOn_log_Gamma`).

Write n = ⌊x⌋.  Log-convexity of Γ gives the two-sided "slope sandwich"

  (x−n)·log n  ≤  log Γ(x+1) − log Γ(n+1)  ≤  (x−n)·log(n+1),

so log Γ(x+1) is pinned to the discrete value log Γ(n+1) up to an error that an
elementary estimate (using only `Real.log_le_sub_one_of_pos`) shows tends to 0.
This is the classical Artin/Bohr–Mollerup route and is far shorter than a Laplace
integral analysis.

## Status
- [x] Discrete → continuous log form (fully verified, 0 sorries, 0 axioms)
- [x] Asymptotic equivalence `~` form
- [x] Slope sandwich from `convexOn_log_Gamma`
- [x] Elementary error estimate `x·log(n/x) + (x−n) → 0`

## Mathlib Dependencies
- `Real.convexOn_log_Gamma`           : log ∘ Γ is convex on (0, ∞)
- `Stirling.factorial_isEquivalent_stirling` : n! ~ √(2πn)·(n/e)^n
- `Real.Gamma_add_one`, `Real.Gamma_pos_of_pos`, `Real.Gamma_nat_eq_factorial`
- `Real.log_le_sub_one_of_pos`        : log y ≤ y − 1
- `tendsto_nat_floor_div_atTop`       : ⌊x⌋/x → 1
-/

namespace StirlingGammaCont

open Real Filter Asymptotics Topology

/-- The logarithm of the Stirling approximation `√(2πy)·(y/e)^y`. -/
noncomputable def logApprox (y : ℝ) : ℝ :=
  (1 / 2) * Real.log (2 * π * y) + y * Real.log y - y

-- ============================================================
-- PART 1: Elementary error estimate
--   −1/⌊x⌋ ≤ x·log(⌊x⌋/x) + (x − ⌊x⌋) ≤ 0
-- ============================================================

/-- Upper bound: `x·log(⌊x⌋/x) + (x − ⌊x⌋) ≤ 0`, from `log y ≤ y − 1`. -/
theorem error_le_zero (x : ℝ) (hx : 1 ≤ x) :
    x * Real.log ((⌊x⌋₊ : ℝ) / x) + (x - (⌊x⌋₊ : ℝ)) ≤ 0 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hn1 : 1 ≤ (⌊x⌋₊ : ℝ) := by
    have : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.mpr hx
    exact_mod_cast this
  have hnx : (0 : ℝ) < (⌊x⌋₊ : ℝ) / x := by positivity
  have hlog : Real.log ((⌊x⌋₊ : ℝ) / x) ≤ (⌊x⌋₊ : ℝ) / x - 1 := log_le_sub_one_of_pos hnx
  have hmul : x * Real.log ((⌊x⌋₊ : ℝ) / x) ≤ x * ((⌊x⌋₊ : ℝ) / x - 1) :=
    mul_le_mul_of_nonneg_left hlog hx0.le
  have heq : x * ((⌊x⌋₊ : ℝ) / x - 1) = (⌊x⌋₊ : ℝ) - x := by field_simp
  nlinarith [hmul, heq]

/-- Lower bound: `−1/⌊x⌋ ≤ x·log(⌊x⌋/x) + (x − ⌊x⌋)`. -/
theorem error_ge (x : ℝ) (hx : 1 ≤ x) :
    -(1 / (⌊x⌋₊ : ℝ)) ≤ x * Real.log ((⌊x⌋₊ : ℝ) / x) + (x - (⌊x⌋₊ : ℝ)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hn1 : 1 ≤ (⌊x⌋₊ : ℝ) := by
    have : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.mpr hx
    exact_mod_cast this
  have hnpos : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by linarith
  have hxn0 : (0 : ℝ) < x / (⌊x⌋₊ : ℝ) := by positivity
  have hlog : Real.log (x / (⌊x⌋₊ : ℝ)) ≤ x / (⌊x⌋₊ : ℝ) - 1 := log_le_sub_one_of_pos hxn0
  have hinv : Real.log (x / (⌊x⌋₊ : ℝ)) = -Real.log ((⌊x⌋₊ : ℝ) / x) := by
    rw [← Real.log_inv]; congr 1; field_simp
  rw [hinv] at hlog
  have h2 : x * (1 - x / (⌊x⌋₊ : ℝ)) ≤ x * Real.log ((⌊x⌋₊ : ℝ) / x) :=
    mul_le_mul_of_nonneg_left (by linarith) hx0.le
  have hfract : x - (⌊x⌋₊ : ℝ) < 1 := by
    have := Nat.lt_floor_add_one x; linarith
  have hfract0 : 0 ≤ x - (⌊x⌋₊ : ℝ) := by
    have := Nat.floor_le hx0.le; linarith
  have key : x * (1 - x / (⌊x⌋₊ : ℝ)) + (x - (⌊x⌋₊ : ℝ))
      = -((x - (⌊x⌋₊ : ℝ)) ^ 2 / (⌊x⌋₊ : ℝ)) := by field_simp; ring
  have hsq : (x - (⌊x⌋₊ : ℝ)) ^ 2 ≤ 1 := by nlinarith [hfract, hfract0]
  have hfin : -(1 / (⌊x⌋₊ : ℝ)) ≤ -((x - (⌊x⌋₊ : ℝ)) ^ 2 / (⌊x⌋₊ : ℝ)) := by
    rw [neg_le_neg_iff, div_le_div_iff_of_pos_right hnpos]; exact hsq
  linarith [h2, key, hfin]

-- ============================================================
-- PART 2: Log-convexity slope sandwich
--   log Γ(n+1) + (x−n)·log n ≤ log Γ(x+1) ≤ log Γ(n+1) + (x−n)·log(n+1)
-- ============================================================

/-- Lower sandwich from convexity (slope monotonicity). -/
theorem sandwich_lower (x : ℝ) (hx : 1 ≤ x) :
    Real.log (Real.Gamma ((⌊x⌋₊ : ℝ) + 1)) + (x - (⌊x⌋₊ : ℝ)) * Real.log (⌊x⌋₊ : ℝ)
      ≤ Real.log (Real.Gamma (x + 1)) := by
  set n : ℝ := (⌊x⌋₊ : ℝ) with hn
  have hn1 : 1 ≤ n := by
    have : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.mpr hx
    rw [hn]; exact_mod_cast this
  have hnle : n ≤ x := by rw [hn]; exact Nat.floor_le (by linarith)
  rcases eq_or_lt_of_le hnle with hxe | hxlt
  · rw [← hxe]; simp
  · have hconv := convexOn_log_Gamma
    have hmemn : n ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
    have hmemx1 : x + 1 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
    have hslope := hconv.slope_mono_adjacent hmemn hmemx1
      (by linarith : n < n + 1) (by linarith : n + 1 < x + 1)
    have hGn : Real.Gamma (n + 1) = n * Real.Gamma n :=
      Real.Gamma_add_one (by linarith : n ≠ 0)
    have hGnpos : 0 < Real.Gamma n := Real.Gamma_pos_of_pos (by linarith)
    have hslopeLeft :
        ((Real.log ∘ Real.Gamma) (n + 1) - (Real.log ∘ Real.Gamma) n) / (n + 1 - n)
          = Real.log n := by
      simp only [Function.comp_apply]
      rw [hGn, Real.log_mul (by linarith : n ≠ 0) (ne_of_gt hGnpos),
          show n + 1 - n = 1 by ring, div_one]
      ring
    have hxn : (0 : ℝ) < x - n := by linarith
    rw [hslopeLeft, show x + 1 - (n + 1) = x - n by ring, le_div_iff₀ hxn] at hslope
    simp only [Function.comp_apply] at hslope
    nlinarith [hslope]

/-- Upper sandwich from convexity (chord above the graph). -/
theorem sandwich_upper (x : ℝ) (hx : 1 ≤ x) :
    Real.log (Real.Gamma (x + 1)) ≤
      Real.log (Real.Gamma ((⌊x⌋₊ : ℝ) + 1)) + (x - (⌊x⌋₊ : ℝ)) * Real.log ((⌊x⌋₊ : ℝ) + 1) := by
  set n : ℝ := (⌊x⌋₊ : ℝ) with hn
  have hn1 : 1 ≤ n := by
    have : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.mpr hx
    rw [hn]; exact_mod_cast this
  have hnle : n ≤ x := by rw [hn]; exact Nat.floor_le (by linarith)
  have hlt : x < n + 1 := by rw [hn]; exact_mod_cast Nat.lt_floor_add_one x
  have hconv := convexOn_log_Gamma
  have hmemn1 : n + 1 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hmemn2 : n + 2 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have ha : (0 : ℝ) ≤ (n + 1) - x := by linarith
  have hb : (0 : ℝ) ≤ x - n := by linarith
  have hab : ((n + 1) - x) + (x - n) = 1 := by ring
  have hchord := hconv.2 hmemn1 hmemn2 ha hb hab
  have hpt : ((n + 1) - x) • (n + 1) + (x - n) • (n + 2) = x + 1 := by
    simp only [smul_eq_mul]; ring
  rw [hpt] at hchord
  simp only [Function.comp_apply, smul_eq_mul] at hchord
  have hGn2 : Real.Gamma (n + 2) = (n + 1) * Real.Gamma (n + 1) := by
    have h : (n + 1) + 1 = n + 2 := by ring
    rw [← h, Real.Gamma_add_one (by linarith : n + 1 ≠ 0)]
  have hGn1pos : 0 < Real.Gamma (n + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hL2 : Real.log (Real.Gamma (n + 2))
      = Real.log (n + 1) + Real.log (Real.Gamma (n + 1)) := by
    rw [hGn2, Real.log_mul (by linarith : n + 1 ≠ 0) (ne_of_gt hGn1pos)]
  rw [hL2] at hchord
  nlinarith [hchord]

-- ============================================================
-- PART 3: Algebraic identity linking the discrete and continuous error
-- ============================================================

/-- The combined error term equals the elementary expression of Part 1
(plus a `½·log(n/x)` correction that also vanishes). -/
theorem error_identity (x : ℝ) (hx : 1 ≤ x) :
    (x - (⌊x⌋₊ : ℝ)) * Real.log (⌊x⌋₊ : ℝ) + logApprox (⌊x⌋₊ : ℝ) - logApprox x
      = (1 / 2) * Real.log ((⌊x⌋₊ : ℝ) / x)
          + (x * Real.log ((⌊x⌋₊ : ℝ) / x) + (x - (⌊x⌋₊ : ℝ))) := by
  set n : ℝ := (⌊x⌋₊ : ℝ) with hn
  have hx0 : (0 : ℝ) < x := by linarith
  have hn1 : 1 ≤ n := by
    have : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.mpr hx
    rw [hn]; exact_mod_cast this
  have hnpos : (0 : ℝ) < n := by linarith
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have e1 : Real.log (2 * π * n) - Real.log (2 * π * x) = Real.log (n / x) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  have e2 : Real.log n - Real.log x = Real.log (n / x) :=
    (Real.log_div (ne_of_gt hnpos) (ne_of_gt hx0)).symm
  simp only [logApprox]
  linear_combination (1 / 2) * e1 + x * e2

-- ============================================================
-- PART 4: Discrete Stirling in log form
-- ============================================================

/-- The discrete Stirling formula, in the form `log Γ(n+1) − logApprox n → 0`. -/
theorem discrete_log_stirling :
    Tendsto (fun n : ℕ => Real.log (Real.Gamma ((n : ℝ) + 1)) - logApprox (n : ℝ))
      atTop (𝓝 0) := by
  have hequiv := Stirling.factorial_isEquivalent_stirling
  have hne : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (2 * (n : ℝ) * π) * ((n : ℝ) / Real.exp 1) ^ n ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have htend1 : Tendsto
      (fun n : ℕ => (Nat.factorial n : ℝ) / (Real.sqrt (2 * (n : ℝ) * π) * ((n : ℝ) / Real.exp 1) ^ n))
      atTop (𝓝 1) := (isEquivalent_iff_tendsto_one hne).mp hequiv
  have htendlog : Tendsto
      (fun n : ℕ =>
        Real.log ((Nat.factorial n : ℝ) / (Real.sqrt (2 * (n : ℝ) * π) * ((n : ℝ) / Real.exp 1) ^ n)))
      atTop (𝓝 0) := by
    have h := (Real.continuousAt_log (one_ne_zero)).tendsto.comp htend1
    simpa using h
  refine Filter.Tendsto.congr' ?_ htendlog
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by positivity
  have hden : (0 : ℝ) < Real.sqrt (2 * (n : ℝ) * π) * ((n : ℝ) / Real.exp 1) ^ n := by positivity
  rw [Real.log_div (ne_of_gt hfac) (ne_of_gt hden),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.sqrt_eq_rpow, Real.log_rpow (by positivity)]
  -- log Γ(n+1) = log n!
  rw [Real.Gamma_nat_eq_factorial]
  -- expand logApprox and n·log(n/e) = n·log n − n
  rw [logApprox, Real.log_div (ne_of_gt hn') (Real.exp_ne_zero 1), Real.log_exp]
  have h2pi : Real.log (2 * π * (n : ℝ)) = Real.log (2 * (n : ℝ) * π) := by
    congr 1; ring
  rw [h2pi]
  ring

-- ============================================================
-- PART 5: The vanishing of the error terms
-- ============================================================

/-- `1/⌊x⌋ → 0`. -/
theorem inv_floor_tendsto : Tendsto (fun x : ℝ => ((⌊x⌋₊ : ℝ))⁻¹) atTop (𝓝 0) := by
  have hfl : Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop (α := ℝ))
  exact hfl.inv_tendsto_atTop

/-- `½·log(⌊x⌋/x) → 0`. -/
theorem half_log_floor_div_tendsto :
    Tendsto (fun x : ℝ => (1 / 2) * Real.log ((⌊x⌋₊ : ℝ) / x)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ) / x) atTop (𝓝 1) := tendsto_nat_floor_div_atTop
  have hlog : Tendsto (fun x : ℝ => Real.log ((⌊x⌋₊ : ℝ) / x)) atTop (𝓝 0) := by
    have h := (Real.continuousAt_log (one_ne_zero)).tendsto.comp hdiv
    simpa using h
  have := hlog.const_mul (1 / 2 : ℝ)
  simpa using this

/-- The elementary error `x·log(⌊x⌋/x) + (x − ⌊x⌋) → 0` (squeeze). -/
theorem error_tendsto :
    Tendsto (fun x : ℝ => x * Real.log ((⌊x⌋₊ : ℝ) / x) + (x - (⌊x⌋₊ : ℝ)))
      atTop (𝓝 0) := by
  have hlo : Tendsto (fun x : ℝ => -((⌊x⌋₊ : ℝ))⁻¹) atTop (𝓝 0) := by
    have := inv_floor_tendsto.neg; simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have := error_ge x hx
    rwa [one_div] at this
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact error_le_zero x hx

/-- The upper-sandwich correction `(x − ⌊x⌋)·(log(⌊x⌋+1) − log ⌊x⌋) → 0` (squeeze). -/
theorem correction_tendsto :
    Tendsto (fun x : ℝ =>
      (x - (⌊x⌋₊ : ℝ)) * (Real.log ((⌊x⌋₊ : ℝ) + 1) - Real.log (⌊x⌋₊ : ℝ)))
      atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds inv_floor_tendsto ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hn1 : 1 ≤ (⌊x⌋₊ : ℝ) := by
      have : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.mpr hx
      exact_mod_cast this
    have hfract0 : 0 ≤ x - (⌊x⌋₊ : ℝ) := by
      have := Nat.floor_le (by linarith : (0:ℝ) ≤ x); linarith
    have hmono : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log ((⌊x⌋₊ : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    exact mul_nonneg hfract0 (by linarith [hmono])
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hn1 : 1 ≤ (⌊x⌋₊ : ℝ) := by
      have : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.mpr hx
      exact_mod_cast this
    have hnpos : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by linarith
    have hfract0 : 0 ≤ x - (⌊x⌋₊ : ℝ) := by
      have := Nat.floor_le hx0.le; linarith
    have hfract1 : x - (⌊x⌋₊ : ℝ) ≤ 1 := by
      have := Nat.lt_floor_add_one x; linarith
    -- log(n+1) − log n = log((n+1)/n) ≤ (n+1)/n − 1 = 1/n
    have hd : Real.log ((⌊x⌋₊ : ℝ) + 1) - Real.log (⌊x⌋₊ : ℝ) ≤ ((⌊x⌋₊ : ℝ))⁻¹ := by
      have hdiv : (0 : ℝ) < ((⌊x⌋₊ : ℝ) + 1) / (⌊x⌋₊ : ℝ) := by positivity
      have hl := log_le_sub_one_of_pos hdiv
      rw [Real.log_div (by linarith) (ne_of_gt hnpos)] at hl
      have hsub : ((⌊x⌋₊ : ℝ) + 1) / (⌊x⌋₊ : ℝ) - 1 = ((⌊x⌋₊ : ℝ))⁻¹ := by
        field_simp; ring
      rw [hsub] at hl; exact hl
    have hmono0 : 0 ≤ Real.log ((⌊x⌋₊ : ℝ) + 1) - Real.log (⌊x⌋₊ : ℝ) := by
      have : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log ((⌊x⌋₊ : ℝ) + 1) :=
        Real.log_le_log hnpos (by linarith)
      linarith
    calc (x - (⌊x⌋₊ : ℝ)) * (Real.log ((⌊x⌋₊ : ℝ) + 1) - Real.log (⌊x⌋₊ : ℝ))
        ≤ 1 * (Real.log ((⌊x⌋₊ : ℝ) + 1) - Real.log (⌊x⌋₊ : ℝ)) := by
          apply mul_le_mul_of_nonneg_right hfract1 hmono0
      _ = Real.log ((⌊x⌋₊ : ℝ) + 1) - Real.log (⌊x⌋₊ : ℝ) := by ring
      _ ≤ ((⌊x⌋₊ : ℝ))⁻¹ := hd

-- ============================================================
-- PART 6: Main result — log form
-- ============================================================

/-- **Continuous Stirling formula (logarithmic form).**
`log Γ(x+1) − (½·log(2πx) + x·log x − x) → 0` as `x → ∞`. -/
theorem log_gamma_continuous_stirling :
    Tendsto (fun x : ℝ => Real.log (Real.Gamma (x + 1)) - logApprox x) atTop (𝓝 0) := by
  -- D(x) := log Γ(⌊x⌋+1) − logApprox ⌊x⌋ → 0
  have hD : Tendsto (fun x : ℝ =>
      Real.log (Real.Gamma ((⌊x⌋₊ : ℝ) + 1)) - logApprox (⌊x⌋₊ : ℝ)) atTop (𝓝 0) :=
    discrete_log_stirling.comp (tendsto_nat_floor_atTop (α := ℝ))
  -- lower bounding function
  have hlo : Tendsto (fun x : ℝ =>
      (Real.log (Real.Gamma ((⌊x⌋₊ : ℝ) + 1)) - logApprox (⌊x⌋₊ : ℝ))
        + ((1 / 2) * Real.log ((⌊x⌋₊ : ℝ) / x)
            + (x * Real.log ((⌊x⌋₊ : ℝ) / x) + (x - (⌊x⌋₊ : ℝ))))) atTop (𝓝 0) := by
    have := hD.add (half_log_floor_div_tendsto.add error_tendsto)
    simpa using this
  -- upper bounding function = lower + correction
  have hhi : Tendsto (fun x : ℝ =>
      ((Real.log (Real.Gamma ((⌊x⌋₊ : ℝ) + 1)) - logApprox (⌊x⌋₊ : ℝ))
        + ((1 / 2) * Real.log ((⌊x⌋₊ : ℝ) / x)
            + (x * Real.log ((⌊x⌋₊ : ℝ) / x) + (x - (⌊x⌋₊ : ℝ)))))
        + (x - (⌊x⌋₊ : ℝ)) * (Real.log ((⌊x⌋₊ : ℝ) + 1) - Real.log (⌊x⌋₊ : ℝ)))
      atTop (𝓝 0) := by
    have := hlo.add correction_tendsto
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · -- lower ≤ target
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hid := error_identity x hx
    have hsw := sandwich_lower x hx
    -- target − lower = (log Γ(x+1)) − (log Γ(n+1) + (x−n) log n)  ≥ 0
    nlinarith [hid, hsw]
  · -- target ≤ upper
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hid := error_identity x hx
    have hsw := sandwich_upper x hx
    nlinarith [hid, hsw]

-- ============================================================
-- PART 7: Main result — asymptotic equivalence
-- ============================================================

/-- `exp(logApprox x) = √(2πx)·(x/e)^x` for `x > 0`. -/
theorem exp_logApprox (x : ℝ) (hx : 0 < x) :
    Real.exp (logApprox x) = Real.sqrt (2 * π * x) * (x / Real.exp 1) ^ x := by
  have h1 : Real.sqrt (2 * π * x) = Real.exp ((1 / 2) * Real.log (2 * π * x)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]; ring_nf
  have h2 : (x / Real.exp 1) ^ x = Real.exp (x * Real.log x - x) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    rw [Real.log_div (ne_of_gt hx) (Real.exp_ne_zero 1), Real.log_exp]; ring
  rw [h1, h2, ← Real.exp_add, logApprox]
  congr 1; ring

/-- **Continuous Stirling formula (asymptotic equivalence).**
`Γ(x+1) ~ √(2πx)·(x/e)^x` as `x → ∞`. This is the headline result; the sibling
entry `stirling-formula-oq-02` proved it only at integer points. -/
theorem gamma_continuous_isEquivalent_stirling :
    (fun x : ℝ => Real.Gamma (x + 1)) ~[atTop]
      fun x : ℝ => Real.sqrt (2 * π * x) * (x / Real.exp 1) ^ x := by
  refine (isEquivalent_iff_tendsto_one ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have : 0 < Real.sqrt (2 * π * x) * (x / Real.exp 1) ^ x := by positivity
    exact ne_of_gt this
  · have hexp : Tendsto
        (fun x : ℝ => Real.exp (Real.log (Real.Gamma (x + 1)) - logApprox x))
        atTop (𝓝 1) := by
      have h := (Real.continuous_exp.tendsto 0).comp log_gamma_continuous_stirling
      simpa using h
    refine hexp.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hΓ : 0 < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos (by linarith)
    rw [Real.exp_sub, Real.exp_log hΓ, exp_logApprox x hx]
    simp [Pi.div_apply]

end StirlingGammaCont
