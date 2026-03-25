/-
# The Classical Limit (1 + x/n)^n → exp(x) (OQ-03-OQ-02)

Research Question: Can we prove the classical limit definition of the exponential
function — lim_{n→∞} (1 + x/n)^n = e^x — from first principles in Lean 4?

Answer: YES. The proof uses three ingredients:
  1. The derivative of log at 1: log'(1) = 1
  2. The slope form: log(1+h)/h → 1 as h → 0
  3. Continuity of exp: if n·log(1+x/n) → x, then exp(n·log(1+x/n)) → exp(x)

This is a result not currently in Mathlib (as of v4.26.0), proved here from
standard Mathlib analysis infrastructure.

What This Proves:
  The main limit theorem, Euler's number as (1+1/n)^n → e, the reciprocal
  limit (1-1/n)^n → e⁻¹, and the compound interest limit for continuous
  compounding, all verified with 0 axioms and 0 sorries.

Parent: BinomialTheoremOQ03 (Binomial Distribution from the Binomial Theorem)

Tags: analysis, exponential, limits, euler-number, compound-interest, mathlib-contribution
-/

import Mathlib

open Filter Topology

namespace ExponentialLimit

/-! ## Part I: The Main Limit Theorem -/

/-- The derivative of log(1+t) at t=0 is 1.
    This is the foundational fact: since log(1) = 0 and (d/dt)log(t)|_{t=1} = 1,
    composing with t ↦ 1+t gives (d/dt)log(1+t)|_{t=0} = 1. -/
theorem hasDerivAt_log_one_plus :
    HasDerivAt (fun t : ℝ => Real.log (1 + t)) 1 (0 : ℝ) := by
  have h1 : HasDerivAt (fun t : ℝ => (1 : ℝ) + t) 1 (0 : ℝ) :=
    (hasDerivAt_id (0 : ℝ)).const_add 1
  have h2 : HasDerivAt Real.log (1 : ℝ)⁻¹ ((fun t : ℝ => 1 + t) (0 : ℝ)) := by
    show HasDerivAt Real.log 1⁻¹ (1 + 0)
    rw [add_zero]
    exact Real.hasDerivAt_log one_ne_zero
  have h3 := h2.comp (0 : ℝ) h1
  simp only [inv_one, mul_one] at h3
  exact h3

/-- The slope of log at 1: log(1+h)/h → 1 as h → 0 (through nonzero values).
    This is the derivative expressed as a difference quotient. -/
theorem tendsto_log_one_plus_div :
    Tendsto (fun h : ℝ => Real.log (1 + h) / h)
    (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
  have hs : Tendsto (slope (fun t : ℝ => Real.log (1 + t)) 0)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
    rw [show nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ = nhds 0 ⊓ 𝓟 {(0 : ℝ)}ᶜ from rfl]
    exact hasDerivAtFilter_iff_tendsto_slope.mp
      (hasDerivAt_log_one_plus.hasDerivAtFilter le_rfl)
  refine hs.congr (fun h => ?_)
  simp [slope, sub_zero, Real.log_one, smul_eq_mul, inv_mul_eq_div]

/-- **The classical limit: (1 + x/n)^n → exp(x) as n → ∞.**

This is the fundamental limit characterization of the exponential function,
connecting discrete compound growth to continuous exponential growth.

**Proof strategy:**
- When x = 0, the result is trivial.
- When x ≠ 0, we use:
  (a) log(1+h)/h → 1 as h → 0 (the derivative of log at 1)
  (b) x/n → 0 through nonzero values, so by composition,
      log(1 + x/n)/(x/n) → 1
  (c) Therefore n·log(1 + x/n) = x · [log(1 + x/n)/(x/n)] → x·1 = x
  (d) By continuity of exp: exp(n·log(1 + x/n)) → exp(x)
  (e) For large n, 1 + x/n > 0, so exp(n·log(1 + x/n)) = (1 + x/n)^n -/
theorem tendsto_one_plus_div_pow_exp (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => (1 + x / (↑n : ℝ)) ^ n)
    Filter.atTop (nhds (Real.exp x)) := by
  -- Case x = 0: (1 + 0/n)^n = 1^n = 1 = exp(0)
  by_cases hx : x = 0
  · subst hx
    simp only [zero_div, add_zero, one_pow, Real.exp_zero]
    exact tendsto_const_nhds
  -- Step 1: x/n → 0 in nhdsWithin 0 {0}ᶜ (approaches 0 but ≠ 0)
  have hxn : Tendsto (fun n : ℕ => x / (↑n : ℝ)) atTop
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
    rw [nhdsWithin, tendsto_inf]
    exact ⟨tendsto_const_div_atTop_nhds_zero_nat x,
      tendsto_principal.mpr (eventually_atTop.mpr ⟨1, fun n hn =>
        div_ne_zero hx (Nat.cast_ne_zero.mpr (by omega))⟩)⟩
  -- Step 2: log(1 + x/n)/(x/n) → 1 by composition with the slope limit
  have hcomp : Tendsto (fun n : ℕ => Real.log (1 + x / ↑n) / (x / ↑n))
      atTop (nhds 1) :=
    tendsto_log_one_plus_div.comp hxn
  -- Step 3: n·log(1 + x/n) = x · [log(1 + x/n)/(x/n)] eventually
  have heq : ∀ᶠ (n : ℕ) in atTop, (↑n : ℝ) * Real.log (1 + x / ↑n) =
      x * (Real.log (1 + x / ↑n) / (x / ↑n)) := by
    filter_upwards [Ici_mem_atTop 1] with n (hn : 1 ≤ n)
    have hn_ne : (↑n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hxdiv : x / (x / (↑n : ℝ)) = ↑n := by field_simp
    set L := Real.log (1 + x / (↑n : ℝ))
    calc ↑n * L = L * ↑n := by ring
      _ = L * (x / (x / ↑n)) := by rw [hxdiv]
      _ = x * (L / (x / ↑n)) := by ring
  -- Step 4: n·log(1 + x/n) → x
  have hlog : Tendsto (fun n : ℕ => (↑n : ℝ) * Real.log (1 + x / ↑n))
      atTop (nhds x) := by
    have h := (tendsto_const_nhds (x := x)).mul hcomp
    rw [mul_one] at h
    exact h.congr' (heq.mono fun n hn => hn.symm)
  -- Step 5: exp(n·log(1 + x/n)) → exp(x) by continuity of exp
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  -- Step 6: exp(n·log(1 + x/n)) = (1 + x/n)^n for large n
  refine hexp.congr' ?_
  filter_upwards [Ici_mem_atTop (Nat.ceil |x| + 1)] with n hn
  simp only [Function.comp]
  have hn_pos : (0 : ℝ) < ↑n := by
    have : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hn
    exact Nat.cast_pos.mpr (by omega)
  have habs : |x| < ↑n := by
    calc |x| ≤ ↑(Nat.ceil |x|) := Nat.le_ceil |x|
      _ < ↑(Nat.ceil |x|) + 1 := by linarith
      _ ≤ ↑n := by exact_mod_cast hn
  have hbase : (0 : ℝ) < 1 + x / ↑n := by
    have hle : -(x / ↑n) ≤ |x / ↑n| := neg_le_abs _
    have hlt : |x / ↑n| < 1 := by
      rw [abs_div, abs_of_pos hn_pos]
      exact (div_lt_one hn_pos).mpr habs
    linarith
  rw [Real.exp_nat_mul, Real.exp_log hbase]

/-! ## Part II: Euler's Number -/

/-- Euler's number as a limit: (1 + 1/n)^n → e.
    The most famous instance of the exponential limit. -/
theorem tendsto_euler :
    Filter.Tendsto (fun n : ℕ => (1 + 1 / (↑n : ℝ)) ^ n)
    Filter.atTop (nhds (Real.exp 1)) :=
  tendsto_one_plus_div_pow_exp 1

/-- The reciprocal limit: (1 - 1/n)^n → e⁻¹.
    Substituting x = -1 in the main limit. -/
theorem tendsto_one_minus_div_pow_inv_e :
    Filter.Tendsto (fun n : ℕ => (1 - 1 / (↑n : ℝ)) ^ n)
    Filter.atTop (nhds (Real.exp (-1))) := by
  have h := tendsto_one_plus_div_pow_exp (-1)
  simp only [neg_div] at h
  exact h.congr (fun n => by ring_nf)

/-- The exponential limit with negative argument: (1 - x/n)^n → exp(-x).
    Models continuous decay or discounting. -/
theorem tendsto_one_minus_div_pow_exp_neg (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => (1 - x / (↑n : ℝ)) ^ n)
    Filter.atTop (nhds (Real.exp (-x))) := by
  have h := tendsto_one_plus_div_pow_exp (-x)
  simp only [neg_div] at h
  exact h.congr (fun n => by ring_nf)

/-! ## Part III: Compound Interest and Continuous Compounding -/

/-- Continuous compounding limit: (1 + r/n)^n → exp(r).
    In finance, if annual rate r is compounded n times per year,
    the effective multiplier approaches exp(r) as n → ∞.
    This is the same as the main theorem, stated for emphasis. -/
theorem continuous_compounding (r : ℝ) :
    Filter.Tendsto (fun n : ℕ => (1 + r / (↑n : ℝ)) ^ n)
    Filter.atTop (nhds (Real.exp r)) :=
  tendsto_one_plus_div_pow_exp r

/-! ## Part III-b: The Inequality 1 + x ≤ exp(x) -/

/-- The fundamental inequality: 1 + x ≤ exp(x) for all x : ℝ.
    This follows from the convexity of exp (or equivalently, exp dominates
    its tangent line at 0). Note: this is `Real.add_one_le_exp` in Mathlib,
    restated here for completeness. -/
theorem one_plus_le_exp (x : ℝ) : 1 + x ≤ Real.exp x := by
  linarith [Real.add_one_le_exp x]

/-- The inequality applied n times gives a bound on partial compounding:
    (1 + x/n)^n ≤ exp(x) for x ≥ 0 and n ≥ 1.
    Each factor (1 + x/n) ≤ exp(x/n), so the product ≤ exp(x/n)^n = exp(x). -/
theorem one_plus_div_pow_le_exp (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (hn : 1 ≤ n) :
    (1 + x / (↑n : ℝ)) ^ n ≤ Real.exp x := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  -- Each factor: 1 + x/n ≤ exp(x/n)
  have hfactor : 1 + x / ↑n ≤ Real.exp (x / ↑n) := one_plus_le_exp (x / ↑n)
  -- Since 1 + x/n ≥ 0 (because x ≥ 0, n ≥ 1)
  have hbase : (0 : ℝ) ≤ 1 + x / ↑n := by positivity
  -- (1 + x/n)^n ≤ exp(x/n)^n
  have hpow : (1 + x / ↑n) ^ n ≤ (Real.exp (x / ↑n)) ^ n :=
    pow_le_pow_left₀ hbase hfactor n
  -- exp(x/n)^n = exp(n · x/n) = exp(x)
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  calc (1 + x / ↑n) ^ n ≤ (Real.exp (x / ↑n)) ^ n := hpow
    _ = Real.exp (↑n * (x / ↑n)) := by rw [← Real.exp_nat_mul]
    _ = Real.exp x := by congr 1; field_simp

/-! ## Part IV: Summary -/

/-- Summary theorem packaging the main results:
    1. The exponential limit
    2. Euler's number limit
    3. The bound (1+x/n)^n ≤ exp(x) for x ≥ 0 -/
theorem exponential_limit_summary :
    -- (1) The exponential limit
    (∀ x : ℝ, Filter.Tendsto (fun n : ℕ => (1 + x / (↑n : ℝ)) ^ n)
      Filter.atTop (nhds (Real.exp x))) ∧
    -- (2) Euler's number limit
    (Filter.Tendsto (fun n : ℕ => (1 + 1 / (↑n : ℝ)) ^ n)
      Filter.atTop (nhds (Real.exp 1))) ∧
    -- (3) Reciprocal limit
    (Filter.Tendsto (fun n : ℕ => (1 - 1 / (↑n : ℝ)) ^ n)
      Filter.atTop (nhds (Real.exp (-1)))) :=
  ⟨tendsto_one_plus_div_pow_exp, tendsto_euler, tendsto_one_minus_div_pow_inv_e⟩

end ExponentialLimit
