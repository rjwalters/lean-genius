import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Stirling's Formula

## What This Proves
Stirling's approximation for factorials:

  n! ~ √(2πn) · (n/e)^n

More precisely, lim(n→∞) n! / [√(2πn) · (n/e)^n] = 1

This is Wiedijk's 100 Theorems #90.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `Stirling` module which provides
  the complete proof of Stirling's formula via the Wallis product.
- **Key Mathlib theorems:**
  - `Stirling.stirlingSeq`: The sequence n!/[√(2n)(n/e)^n] converging to √π
  - `Stirling.tendsto_stirlingSeq_sqrt_pi`: stirlingSeq → √π as n → ∞
  - `Stirling.factorial_isEquivalent_stirling`: n! ~ √(2πn)(n/e)^n
- **Original Contributions:** Pedagogical presentation, bounds for applications,
  and connection to binomial coefficient approximations.

## Status
- [x] Complete proof (main Stirling formula)
- [x] Uses Mathlib for main result
- [x] Proves bounds and corollaries
- [x] Pedagogical examples
- [x] No sorries (uses 1 axiom for refined error bound)

## Mathlib Dependencies
- `Stirling.stirlingSeq` : The sequence n!/[√(2n)(n/e)^n]
- `Stirling.tendsto_stirlingSeq_sqrt_pi` : Convergence to √π
- `Stirling.factorial_isEquivalent_stirling` : Asymptotic equivalence
- `Stirling.sqrt_pi_le_stirlingSeq` : Lower bound by √π
- `Filter.Tendsto`, `Asymptotics.IsEquivalent` : Limit and asymptotic machinery

Historical Note: The formula is named after James Stirling (1730), but the leading
constant √(2π) was discovered by de Moivre. Stirling refined the formula with the
full asymptotic expansion n! ~ √(2πn)(n/e)^n(1 + 1/(12n) + 1/(288n²) - ...).
-/

namespace StirlingFormula

open Stirling Real Filter

-- ============================================================
-- PART 1: The Stirling Sequence
-- ============================================================

/-!
### The Stirling Sequence

Define stirlingSeq(n) = n!/[√(2n)(n/e)^n]

This sequence converges to √π, which is equivalent to saying:
  n! ~ √(2πn)(n/e)^n
-/

/-- The Stirling sequence n!/[√(2n)(n/e)^n] is defined for n ≥ 1 -/
theorem stirlingSeq_defined (n : ℕ) (hn : n ≥ 1) :
    stirlingSeq n = n.factorial / (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := by
  rfl

/-- The Stirling sequence is positive for n ≥ 1 -/
theorem stirlingSeq_pos (n : ℕ) (hn : 1 ≤ n) : 0 < stirlingSeq n := by
  unfold stirlingSeq
  apply div_pos
  · exact Nat.cast_pos.mpr (Nat.factorial_pos n)
  · apply mul_pos
    · apply Real.sqrt_pos.mpr
      have : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      linarith
    · apply pow_pos
      apply div_pos (Nat.cast_pos.mpr hn) (Real.exp_pos 1)

-- ============================================================
-- PART 2: Convergence to √π
-- ============================================================

/-!
### Convergence of the Stirling Sequence

The key result: stirlingSeq(n) → √π as n → ∞

This is proven in Mathlib via the Wallis product:
  π/2 = ∏(n=1 to ∞) (4n²)/(4n² - 1)
-/

/-- **The Stirling sequence converges to √π**

This is the central result from which Stirling's formula follows. -/
theorem stirlingSeq_tendsto_sqrt_pi :
    Tendsto stirlingSeq atTop (nhds (Real.sqrt π)) := by
  exact Stirling.tendsto_stirlingSeq_sqrt_pi

/-- Equivalent statement: the ratio n!/(√(2n)(n/e)^n) approaches √π -/
theorem factorial_ratio_tendsto :
    Tendsto (fun n : ℕ => n.factorial / (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n))
      atTop (nhds (Real.sqrt π)) := by
  exact Stirling.tendsto_stirlingSeq_sqrt_pi

-- ============================================================
-- PART 3: Stirling's Asymptotic Formula
-- ============================================================

/-!
### The Asymptotic Equivalence

Stirling's formula as an asymptotic equivalence:
  n! ~ √(2πn) · (n/e)^n

Meaning: the ratio of these quantities approaches 1.
-/

/-- **Stirling's Formula** (Wiedijk #90)

n! is asymptotically equivalent to √(2πn) · (n/e)^n

This means lim(n→∞) n! / [√(2πn)(n/e)^n] = 1 -/
theorem stirling_formula :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (n.factorial : ℝ))
      (fun n : ℕ => Real.sqrt (2 * π * n) * (n / Real.exp 1) ^ n) := by
  -- Mathlib uses √(2 * n * π), we use √(2 * π * n) (same value since multiplication commutes)
  have h := Stirling.factorial_isEquivalent_stirling
  have heq : (fun n : ℕ => Real.sqrt (2 * π * ↑n) * (↑n / Real.exp 1) ^ n) =
             (fun n : ℕ => Real.sqrt (2 * ↑n * π) * (↑n / Real.exp 1) ^ n) := by
    funext n; congr 1; ring
  rw [heq]
  exact h

-- ============================================================
-- PART 4: Bounds from Stirling's Formula
-- ============================================================

/-!
### Useful Bounds

For practical applications, we need explicit bounds on n!.
-/

/-- The Stirling sequence is bounded below by √π for n ≥ 1 -/
theorem sqrt_pi_le_stirlingSeq (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt π ≤ stirlingSeq n := by
  -- stirlingSeq is antitone (decreasing) and converges to √π, so all terms ≥ √π
  -- This is a standard result: for antitone sequences, limit = infimum
  have htend := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hanti := Stirling.stirlingSeq'_antitone
  -- For n ≥ 1, stirlingSeq n = stirlingSeq ((n-1) + 1) = (stirlingSeq ∘ succ) (n - 1)
  have heq : stirlingSeq n = (stirlingSeq ∘ Nat.succ) (n - 1) := by
    simp only [Function.comp_apply]; congr 1; omega
  rw [heq]
  -- Use Antitone.tendsto_atTop_ciInf: for antitone bounded-below sequence,
  -- the limit equals the infimum, so all terms are ≥ limit
  have hbdd : BddBelow (Set.range (stirlingSeq ∘ Nat.succ)) := by
    obtain ⟨a, ha_pos, ha⟩ := Stirling.stirlingSeq'_bounded_by_pos_constant
    refine ⟨a, ?_⟩
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    exact ha k
  -- The infimum of the antitone sequence equals its limit
  have hinf := tendsto_atTop_ciInf hanti hbdd
  -- Since both htend (after composing) and hinf converge, limit = infimum = √π
  have hlim : ⨅ k, (stirlingSeq ∘ Nat.succ) k = Real.sqrt π := by
    have htend' : Tendsto (stirlingSeq ∘ Nat.succ) atTop (nhds (Real.sqrt π)) := by
      exact htend.comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique hinf htend'
  -- All terms are ≥ infimum = √π
  rw [← hlim]
  exact ciInf_le hbdd (n - 1)

/-- Lower bound on n!: n! ≥ √π · √(2n) · (n/e)^n for n ≥ 1

This is equivalent to: n! ≥ √(2πn) · (n/e)^n -/
theorem factorial_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (2 * π * n) * (n / Real.exp 1) ^ n ≤ n.factorial := by
  -- From stirlingSeq(n) ≥ √π, we get n! ≥ √π · √(2n) · (n/e)^n
  have hsqrt := sqrt_pi_le_stirlingSeq n hn
  have hseq_def : stirlingSeq n = n.factorial / (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := rfl
  have hpos : 0 < Real.sqrt (2 * n) * (n / Real.exp 1) ^ n := by
    apply mul_pos
    · apply Real.sqrt_pos.mpr
      have : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      linarith
    · apply pow_pos
      apply div_pos (Nat.cast_pos.mpr hn) (Real.exp_pos 1)
  -- stirlingSeq n ≥ √π means n!/[√(2n)·(n/e)^n] ≥ √π
  -- So n! ≥ √π · √(2n) · (n/e)^n
  rw [hseq_def] at hsqrt
  have h := (le_div_iff hpos).mp hsqrt
  -- h : √π * (√(2n) · (n/e)^n) ≤ n!
  -- √(2πn) = √π · √(2n)
  have hsqrt_eq : Real.sqrt (2 * π * n) = Real.sqrt π * Real.sqrt (2 * n) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ π)]
    congr 1; ring
  rw [hsqrt_eq]
  -- Need: √π · √(2n) · (n/e)^n ≤ n!
  -- This equals √π · (√(2n) · (n/e)^n) by associativity
  have hassoc : Real.sqrt π * Real.sqrt (2 * ↑n) * (↑n / Real.exp 1) ^ n =
                Real.sqrt π * (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := by ring
  rw [hassoc]
  exact h

/-- Lower bound on log(n!) for n ≥ 1 -/
theorem log_factorial_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log (Real.sqrt (2 * π * n)) + n * Real.log (n / Real.exp 1) ≤
      Real.log (n.factorial) := by
  have hfact := factorial_lower_bound n hn
  have hpos_approx : 0 < Real.sqrt (2 * π * n) * (n / Real.exp 1) ^ n := by
    apply mul_pos
    · apply Real.sqrt_pos.mpr; positivity
    · apply pow_pos; apply div_pos (Nat.cast_pos.mpr hn) (Real.exp_pos 1)
  have hpos_fact : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  rw [← Real.log_le_log_iff hpos_approx hpos_fact] at hfact
  convert hfact using 1
  rw [Real.log_mul (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
      (ne_of_gt (pow_pos (div_pos (Nat.cast_pos.mpr hn) (Real.exp_pos 1)) n))]
  rw [Real.log_pow]

-- ============================================================
-- PART 5: Classical Approximation Formula
-- ============================================================

/-!
### The Classic Approximation

For large n, we can use √(2πn)(n/e)^n as an approximation to n!.
-/

/-- The Stirling approximation function -/
noncomputable def stirlingApprox (n : ℕ) : ℝ :=
  Real.sqrt (2 * π * n) * (n / Real.exp 1) ^ n

/-- For n ≥ 1, the Stirling approximation is positive -/
theorem stirlingApprox_pos (n : ℕ) (hn : 1 ≤ n) : 0 < stirlingApprox n := by
  unfold stirlingApprox
  apply mul_pos
  · apply Real.sqrt_pos.mpr
    apply mul_pos
    · apply mul_pos <;> positivity
    · exact Nat.cast_pos.mpr hn
  · apply pow_pos
    apply div_pos
    · exact Nat.cast_pos.mpr hn
    · exact Real.exp_pos 1

/-- The ratio n!/stirlingApprox(n) → 1 as n → ∞ -/
theorem factorial_div_approx_tendsto_one :
    Tendsto (fun n : ℕ => n.factorial / stirlingApprox n) atTop (nhds 1) := by
  have h := stirling_formula
  -- IsEquivalent means f/g → 1 when g is eventually nonzero
  have hne : ∀ᶠ n in atTop, stirlingApprox n ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact ne_of_gt (stirlingApprox_pos n hn)
  exact Asymptotics.isEquivalent_iff_tendsto_one hne |>.mp h

-- ============================================================
-- PART 6: Numerical Examples
-- ============================================================

/-- Example: 10! = 3,628,800 vs Stirling ≈ 3,598,696 (error ~0.8%) -/
theorem factorial_10 : Nat.factorial 10 = 3628800 := by native_decide

/-- Example: 20! = 2,432,902,008,176,640,000 -/
theorem factorial_20 : Nat.factorial 20 = 2432902008176640000 := by native_decide

/-- The relative error in Stirling's approximation is O(1/n)

More precisely, n!/stirlingApprox(n) = 1 + 1/(12n) + O(1/n²)

Proof sketch: n!/stirlingApprox(n) = stirlingSeq(n)/√π where stirlingSeq is
antitone (decreasing) with limit √π. At n=1, the ratio is e/√(2π) ≈ 1.084,
so ratio - 1 ≈ 0.084 < 1 = 1/1. For n ≥ 2, ratio is smaller by antitonicity,
giving ratio - 1 < 0.5 ≤ 1/2 ≤ 1/n. -/

-- ============================================================
-- PART 6.5: Proof Infrastructure for Error Bound
-- ============================================================

/-! ### Telescoping Log Bound

We prove stirlingSeq(n)/√π - 1 ≤ 1/n for n ≥ 2 by:
1. Bounding log(stirlingSeq(n)) - log(√π) ≤ 1/(4(n-1)) via telescoping
2. Converting the log bound to a linear bound via (1-x)exp(x) ≤ 1
-/

/-- For m ≥ 1 and any L:
    log(stirlingSeq(m+1)) - log(stirlingSeq(m+L+1)) ≤ 1/(4m).

    Proof by induction on L, using Mathlib's per-step bound
    `log_stirlingSeq_sub_log_stirlingSeq_succ` and the comparison
    1/(k+1)² ≤ 1/(k(k+1)) = 1/k - 1/(k+1). -/
private lemma log_stirlingSeq_ratio_bound (m : ℕ) (hm : 1 ≤ m) (L : ℕ) :
    Real.log (stirlingSeq (m + 1)) - Real.log (stirlingSeq (m + L + 1)) ≤
      1 / (4 * (m : ℝ)) := by
  -- Prove the stronger bound: ≤ (1/4)(1/m - 1/(m+L))
  suffices hsuff : Real.log (stirlingSeq (m + 1)) - Real.log (stirlingSeq (m + L + 1)) ≤
      1 / 4 * (1 / (m : ℝ) - 1 / ↑(m + L)) by
    have : (0 : ℝ) ≤ 1 / ↑(m + L) := by positivity
    linarith
  induction L with
  | zero => simp
  | succ L ih =>
    -- Split: log(m+1) - log(m+L+2) = [log(m+1) - log(m+L+1)] + [log(m+L+1) - log(m+L+2)]
    have hsplit : Real.log (stirlingSeq (m + 1)) - Real.log (stirlingSeq (m + (L + 1) + 1)) =
        (Real.log (stirlingSeq (m + 1)) - Real.log (stirlingSeq (m + L + 1))) +
        (Real.log (stirlingSeq (m + L + 1)) - Real.log (stirlingSeq (m + L + 2))) := by
      have : m + (L + 1) + 1 = m + L + 2 := by omega
      rw [this]; ring
    rw [hsplit]
    -- Per-step bound from Mathlib
    have hstep : Real.log (stirlingSeq (m + L + 1)) - Real.log (stirlingSeq (m + L + 2)) ≤
        1 / (4 * (↑(m + L + 1) : ℝ) ^ 2) :=
      Stirling.log_stirlingSeq_sub_log_stirlingSeq_succ (m + L)
    -- Comparison: 1/(k+1)² ≤ 1/k - 1/(k+1) where k = m+L
    have hmL_pos : (0 : ℝ) < ↑(m + L) := by positivity
    have hmL1_pos : (0 : ℝ) < ↑(m + L + 1) := by positivity
    have hcomp : (1 : ℝ) / (4 * ↑(m + L + 1) ^ 2) ≤
        1 / 4 * (1 / ↑(m + L) - 1 / ↑(m + L + 1)) := by
      -- 1/4 * (1/k - 1/(k+1)) = 1/(4k(k+1)) and 1/(4(k+1)²) ≤ 1/(4k(k+1))
      rw [show (1 : ℝ) / ↑(m + L) - 1 / ↑(m + L + 1) =
          1 / (↑(m + L) * ↑(m + L + 1)) from by field_simp]
      rw [show (1 : ℝ) / 4 * (1 / (↑(m + L) * ↑(m + L + 1))) =
          1 / (4 * (↑(m + L) * ↑(m + L + 1))) from by ring]
      -- Now: 1/(4(k+1)²) ≤ 1/(4k(k+1)), i.e., k(k+1) ≤ (k+1)², i.e., k ≤ k+1
      rw [div_le_div_iff (by positivity) (by positivity)]
      nlinarith [show (↑(m + L) : ℝ) ≤ ↑(m + L + 1) from by exact_mod_cast Nat.le_succ _]
    -- Combine with telescope: 1/4 * (1/m - 1/(m+(L+1))) = 1/4 * (1/m - 1/(m+L)) + 1/4 * (1/(m+L) - 1/(m+L+1))
    have hdecomp : (1 : ℝ) / 4 * (1 / ↑m - 1 / ↑(m + (L + 1))) =
        1 / 4 * (1 / ↑m - 1 / ↑(m + L)) + 1 / 4 * (1 / ↑(m + L) - 1 / ↑(m + L + 1)) := by
      have h_eq : (↑(m + (L + 1)) : ℝ) = ↑(m + L + 1) := by norm_cast
      rw [h_eq]; field_simp; ring
    rw [hdecomp]
    linarith

/-- For m ≥ 1: log(stirlingSeq(m+1)) - log(√π) ≤ 1/(4m).
    Takes the limit of `log_stirlingSeq_ratio_bound` as L → ∞. -/
private lemma log_stirlingSeq_sub_log_sqrt_pi_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (stirlingSeq (m + 1)) - Real.log (Real.sqrt π) ≤ 1 / (4 * (m : ℝ)) := by
  -- stirlingSeq(m + L + 1) → √π as L → ∞
  have htend_seq : Tendsto (fun L : ℕ => stirlingSeq (m + L + 1)) atTop (nhds (Real.sqrt π)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp
      (Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩)
  -- log(stirlingSeq(m + L + 1)) → log(√π)
  have htend_log : Tendsto (fun L => Real.log (stirlingSeq (m + L + 1))) atTop
      (nhds (Real.log (Real.sqrt π))) := by
    have hcont : ContinuousAt Real.log (Real.sqrt π) :=
      Real.continuousAt_log (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))
    exact hcont.tendsto.comp htend_seq
  -- The difference tends to log(stirlingSeq(m+1)) - log(√π)
  have htend_diff : Tendsto (fun L => Real.log (stirlingSeq (m + 1)) -
      Real.log (stirlingSeq (m + L + 1))) atTop
      (nhds (Real.log (stirlingSeq (m + 1)) - Real.log (Real.sqrt π))) :=
    tendsto_const_nhds.sub htend_log
  -- Each term ≤ 1/(4m), so the limit ≤ 1/(4m)
  exact le_of_tendsto' htend_diff (fun L => log_stirlingSeq_ratio_bound m hm L)

/-- For x ≥ 0: (1 - x) * exp(x) ≤ 1.
    Follows from `add_one_le_exp` applied to -x. -/
private lemma one_sub_mul_exp_le_one {x : ℝ} (hx : 0 ≤ x) : (1 - x) * Real.exp x ≤ 1 := by
  by_cases hle : x ≤ 1
  · -- 0 ≤ x ≤ 1: from add_one_le_exp(-x) we get 1 - x ≤ exp(-x)
    calc (1 - x) * Real.exp x
        ≤ Real.exp (-x) * Real.exp x :=
          mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (-x)])
            (le_of_lt (Real.exp_pos x))
      _ = Real.exp 0 := by rw [← Real.exp_add]; ring_nf
      _ = 1 := Real.exp_zero
  · -- x > 1: (1-x) < 0, so (1-x)*exp(x) < 0 < 1
    push_neg at hle
    linarith [mul_neg_of_neg_of_pos (by linarith : 1 - x < 0) (Real.exp_pos x)]

/-- **Stirling error bound for n ≥ 2** (proved, replacing former axiom).

    For n ≥ 2: stirlingSeq n / √π - 1 ≤ 1/n

    **Proof**: From telescoping log bounds in Mathlib:
    - log(stirlingSeq n / √π) ≤ 1/(4(n-1)) via summing per-step bounds
    - exp(1/(4(n-1))) ≤ 1/(1 - 1/(4(n-1))) via (1-x)exp(x) ≤ 1
    - 1/(4(n-1)-1) = 1/(4n-5) ≤ 1/n for n ≥ 2 -/
theorem stirling_error_bound_ge_2 (n : ℕ) (hn : n ≥ 2) :
    Stirling.stirlingSeq n / Real.sqrt Real.pi - 1 ≤ 1 / n := by
  -- Set m = n - 1 ≥ 1
  set m := n - 1 with hm_def
  have hm : 1 ≤ m := by omega
  have hn_eq : n = m + 1 := by omega
  have hn_pos : (0 : ℝ) < ↑n := by positivity
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr (by omega)
  have hpi_pos : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  -- stirlingSeq(n)/√π ≥ 1 (from Mathlib's lower bound)
  have hratio_ge : 1 ≤ stirlingSeq n / Real.sqrt π := by
    rw [one_le_div hpi_pos]
    exact Stirling.sqrt_pi_le_stirlingSeq (by omega : n ≠ 0)
  set r := stirlingSeq n / Real.sqrt π with hr_def
  have hr_pos : 0 < r := lt_of_lt_of_le one_pos hratio_ge
  -- Step 1: Log bound: log(r) ≤ 1/(4m)
  have hlog : Real.log r ≤ 1 / (4 * ↑m) := by
    rw [hr_def, Real.log_div (ne_of_gt (stirlingSeq_pos n (by omega)))
      (ne_of_gt hpi_pos), hn_eq]
    exact log_stirlingSeq_sub_log_sqrt_pi_le m hm
  -- Step 2: r ≤ exp(1/(4m))
  have hr_exp : r ≤ Real.exp (1 / (4 * ↑m)) := by
    calc r = Real.exp (Real.log r) := (Real.exp_log hr_pos).symm
      _ ≤ Real.exp (1 / (4 * ↑m)) := Real.exp_le_exp.mpr hlog
  -- Step 3: exp(x) ≤ 1/(1-x) for x = 1/(4m) via (1-x)exp(x) ≤ 1
  set x := 1 / (4 * (m : ℝ)) with hx_def
  have hx_pos : 0 < x := by positivity
  have hx_lt : x < 1 := by
    rw [hx_def, div_lt_one (by positivity : (0 : ℝ) < 4 * ↑m)]; linarith
  have h1mx : 0 < 1 - x := by linarith
  have hexp_inv : Real.exp x ≤ 1 / (1 - x) := by
    rw [le_div_iff h1mx]
    exact one_sub_mul_exp_le_one (le_of_lt hx_pos)
  -- Step 4: r - 1 ≤ x/(1-x)
  have hr_bound : r - 1 ≤ x / (1 - x) := by
    have h1 : r ≤ 1 / (1 - x) := le_trans hr_exp hexp_inv
    linarith [div_sub_one (ne_of_gt h1mx)]
  -- Step 5: x/(1-x) = 1/(4m-1) ≤ 1/n
  suffices hfin : x / (1 - x) ≤ 1 / ↑n from linarith
  -- Simplify x/(1-x) = 1/(4m-1)
  have h4m1 : (0 : ℝ) < 4 * ↑m - 1 := by linarith
  have hxsimp : x / (1 - x) = 1 / (4 * ↑m - 1) := by
    rw [hx_def]; field_simp
  rw [hxsimp, div_le_div_iff h4m1 hn_pos, one_mul, one_mul]
  -- Goal: ↑n ≤ 4 * ↑m - 1
  -- m + 1 = n, so 4m - 1 = 4(n-1) - 1 = 4n - 5 ≥ n for n ≥ 2
  have hmn : (↑m : ℝ) + 1 = ↑n := by exact_mod_cast (show m + 1 = n from by omega)
  linarith [show (n : ℝ) ≥ 2 from by exact_mod_cast hn]

theorem stirling_error_bound :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n →
      |n.factorial / stirlingApprox n - 1| ≤ C / n := by
  use 1
  refine ⟨by norm_num, fun n hn => ?_⟩
  -- Key identity: n!/stirlingApprox(n) = stirlingSeq(n)/√π
  have hratio : n.factorial / stirlingApprox n = stirlingSeq n / Real.sqrt π := by
    unfold stirlingApprox stirlingSeq
    rw [div_div]
    congr 1
    have h1 : Real.sqrt (2 * π * n) = Real.sqrt (2 * n) * Real.sqrt π := by
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * n)]
      congr 1; ring
    rw [h1]
    ring
  rw [hratio]
  -- Since stirlingSeq n ≥ √π, the ratio is ≥ 1
  have hge1 : stirlingSeq n / Real.sqrt π ≥ 1 := by
    rw [ge_iff_le, one_le_div (Real.sqrt_pos.mpr Real.pi_pos)]
    exact sqrt_pi_le_stirlingSeq n hn
  -- So |ratio - 1| = ratio - 1
  rw [abs_of_nonneg (by linarith : stirlingSeq n / Real.sqrt π - 1 ≥ 0)]
  -- stirlingSeq is antitone (decreasing), so stirlingSeq n ≤ stirlingSeq 1 for n ≥ 1
  have hanti := Stirling.stirlingSeq'_antitone
  -- stirlingSeq n ≤ stirlingSeq 1 for n ≥ 1 (from antitonicity of stirlingSeq' = stirlingSeq ∘ succ)
  have hbound : stirlingSeq n ≤ stirlingSeq 1 := by
    rcases eq_or_lt_of_le hn with h | h
    · rw [← h]
    · -- n ≥ 2, so n-1 ≥ 1, and stirlingSeq n = stirlingSeq' (n-1)
      have hn2 : n ≥ 2 := h
      have heq : stirlingSeq n = (stirlingSeq ∘ Nat.succ) (n - 1) := by
        simp only [Function.comp_apply]
        congr 1
        omega
      have heq1 : stirlingSeq 1 = (stirlingSeq ∘ Nat.succ) 0 := by simp
      rw [heq, heq1]
      apply hanti
      omega
  -- So stirlingSeq n / √π ≤ stirlingSeq 1 / √π
  have hpi_pos : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hupper : stirlingSeq n / Real.sqrt π ≤ stirlingSeq 1 / Real.sqrt π := by
    apply div_le_div_of_nonneg_right hbound (le_of_lt hpi_pos)
  -- We need: stirlingSeq n / √π - 1 ≤ 1/n
  --
  -- The refined asymptotic: stirlingSeq n / √π = 1 + 1/(12n) + O(1/n²)
  -- So stirlingSeq n / √π - 1 ≈ 1/(12n) ≤ 1/n for all n ≥ 1.
  --
  -- Proof approach: Use Mathlib's log bounds. From log_stirlingSeq_sub_log_stirlingSeq_succ:
  --   log(stirlingSeq (n+1)) - log(stirlingSeq (n+2)) ≤ 1/(4(n+1)²)
  -- Summing from k=n-1 to ∞:
  --   log(stirlingSeq n) - log(√π) ≤ Σ_{k≥n-1} 1/(4(k+1)²) ≤ 1/(4(n-1))
  -- Hence: stirlingSeq n / √π ≤ exp(1/(4(n-1))) ≤ 1 + 1/(2(n-1)) for n ≥ 2.
  -- For n = 1: Direct numerical bound shows stirlingSeq 1 / √π - 1 ≈ 0.084 < 1.
  --
  -- Full formalization requires careful orchestration of these bounds.
  -- We use the refined log bound approach from Mathlib.
  have h_bound : stirlingSeq n / Real.sqrt π - 1 ≤ 1 / n := by
    -- Use the telescoping log bound from Mathlib
    -- log(stirlingSeq n) - log(√π) = Σ_{k≥n} [log(stirlingSeq k) - log(stirlingSeq (k+1))]
    -- Each term is bounded by 1/(4k²), so sum ≤ 1/(4(n-1)) for n ≥ 2.
    -- For n = 1, direct computation.
    rcases eq_or_lt_of_le hn with rfl | hn2
    · -- Case n = 1: stirlingSeq 1 / √π - 1 = e/√(2π) - 1 ≈ 0.084 ≤ 1
      rw [Nat.cast_one, div_one]
      rw [Stirling.stirlingSeq_one]
      have he : Real.exp 1 < 2.72 := lt_trans exp_one_lt_d9 (by norm_num)
      have hpi : Real.pi > 3.14 := pi_gt_314
      have h2pi_gt : 2 * Real.pi > 6.28 := by
        have h1 : (2 : ℝ) * 3.14 = 6.28 := by norm_num
        calc 2 * Real.pi > 2 * 3.14 := by linarith
          _ = 6.28 := h1
      have hsqrt_2pi : Real.sqrt (2 * Real.pi) > 2.5 := by
        have h1 : (2.5 : ℝ) ^ 2 = 6.25 := by norm_num
        have h2 : (6.25 : ℝ) < 2 * Real.pi := by
          have h3 : (2 : ℝ) * 3.14 = 6.28 := by norm_num
          calc (6.25 : ℝ) < 6.28 := by norm_num
            _ = 2 * 3.14 := h3.symm
            _ < 2 * Real.pi := by linarith
        calc (2.5 : ℝ) = Real.sqrt (2.5 ^ 2) := by rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.5)]
          _ = Real.sqrt 6.25 := by rw [h1]
          _ < Real.sqrt (2 * Real.pi) := Real.sqrt_lt_sqrt (by norm_num) h2
      have hsqrt_eq : Real.sqrt 2 * Real.sqrt Real.pi = Real.sqrt (2 * Real.pi) := by
        rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [div_sub_one (ne_of_gt hpi_pos)]
      have hcalc : (Real.exp 1 / Real.sqrt 2 - Real.sqrt Real.pi) / Real.sqrt Real.pi
          = Real.exp 1 / (Real.sqrt 2 * Real.sqrt Real.pi) - 1 := by
            have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
            field_simp [ne_of_gt hpi_pos, ne_of_gt hsqrt2_pos]
      rw [hcalc, hsqrt_eq]
      have hle : Real.exp 1 / Real.sqrt (2 * Real.pi) - 1 ≤ 2.72 / 2.5 - 1 := by
        have hexp_le : Real.exp 1 ≤ 2.72 := le_of_lt he
        have hsqrt_le : (2.5 : ℝ) ≤ Real.sqrt (2 * Real.pi) := le_of_lt hsqrt_2pi
        have h2pi_pos : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
        have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi_pos
        have h25_pos : (0 : ℝ) < 2.5 := by norm_num
        calc Real.exp 1 / Real.sqrt (2 * Real.pi) - 1
            ≤ 2.72 / Real.sqrt (2 * Real.pi) - 1 := by gcongr
          _ ≤ 2.72 / 2.5 - 1 := by gcongr
      calc Real.exp 1 / Real.sqrt (2 * Real.pi) - 1
          ≤ 2.72 / 2.5 - 1 := hle
        _ ≤ 1 := by norm_num
    · -- Case n ≥ 2: Use telescoping log bound from Mathlib
      -- From log_stirlingSeq_sub_log_stirlingSeq_succ:
      --   log(stirlingSeq (k+1)) - log(stirlingSeq (k+2)) ≤ 1/(4(k+1)²)
      -- Summing from k = n-1 to ∞ gives: log(stirlingSeq n) - log(√π) ≤ Σ 1/(4k²) ≤ 1/(2n)
      -- Then exp(1/(2n)) ≤ 1 + 1/n gives the result.
      --
      -- Full formalization requires summing the geometric series bound.
      -- We use a simpler approach: the bound is proven for C = 1 which suffices.
      -- For any n ≥ 2, the relative error is at most ~8.4% (at n=1) and decreases.
      -- Since 0.084 < 1/2 ≤ 1/n for n ≥ 2, antitonicity gives the result.
      have hanti := Stirling.stirlingSeq'_antitone
      -- Use bound at n = 1: stirlingSeq n ≤ stirlingSeq 1 for all n ≥ 1
      have hbound_1 : stirlingSeq n ≤ stirlingSeq 1 := hbound
      -- stirlingSeq 1 / √π - 1 ≈ 0.084 (proven in n=1 case above)
      -- For n ≥ 2, by antitonicity: stirlingSeq n / √π - 1 ≤ stirlingSeq 1 / √π - 1 ≤ 1
      -- But we need ≤ 1/n. The key insight: stirlingSeq n / √π - 1 < 0.1 for all n ≥ 1
      -- and 0.1 ≤ 1/n iff n ≤ 10. For n > 10, stirlingSeq n is even closer to √π.
      --
      -- Rigorous proof: Use log bound from Mathlib.
      -- log(stirlingSeq n / √π) = Σ_{k≥n} [log(stirlingSeq k) - log(stirlingSeq (k+1))]
      -- Each term is ≤ 1/(4k²), sum is ≤ 1/(2(n-1)) for n ≥ 2.
      -- exp(1/(2(n-1))) - 1 ≤ 1/n follows from exp(x) ≤ 1 + 2x for small x.
      --
      -- TODO: The full proof requires careful summation of Mathlib's log bounds.
      -- For now, we note that C = 1 suffices for the asymptotic statement.
      have hpi_pos : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
      -- Since stirlingSeq n → √π and stirlingSeq n ≥ √π, the difference shrinks to 0
      -- The bound 1/n works because the error decreases faster than 1/n grows
      -- This follows from the 1/(12n) asymptotic expansion of Stirling's formula
      exact stirling_error_bound_ge_2 n hn2
  exact h_bound

-- ============================================================
-- PART 7: Applications
-- ============================================================

/-!
### Applications of Stirling's Formula

1. **Binomial coefficients**: C(n,k) ≈ n^n / (k^k · (n-k)^(n-k)) for large n
2. **Entropy calculations**: log(n!) ≈ n log n - n + (1/2) log(2πn)
3. **Probability theory**: Central limit theorem derivations
4. **Statistical mechanics**: Boltzmann entropy and thermodynamics
-/

/-- log(n!) ≈ n log n - n + (1/2) log(2πn)

This is the log-form of Stirling's approximation, useful for entropy. -/
theorem log_factorial_approx (n : ℕ) (hn : 1 ≤ n) :
    Real.log n.factorial =
      Real.log (stirlingSeq n) + Real.log (Real.sqrt (2 * n)) +
        n * Real.log n - n := by
  -- From stirlingSeq = n!/[√(2n)(n/e)^n]
  -- log(n!) = log(stirlingSeq) + log(√(2n)) + n·log(n/e)
  --         = log(stirlingSeq) + log(√(2n)) + n·log(n) - n
  have h1 : n.factorial = stirlingSeq n * (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := by
    unfold stirlingSeq
    field_simp
  rw [h1]
  have hpos1 : 0 < stirlingSeq n := stirlingSeq_pos n hn
  have hpos2 : 0 < Real.sqrt (2 * n) := by
    apply Real.sqrt_pos.mpr
    have : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    linarith
  have hpos3 : 0 < (n / Real.exp 1) ^ n := by
    apply pow_pos
    apply div_pos
    · exact Nat.cast_pos.mpr hn
    · exact Real.exp_pos 1
  rw [Real.log_mul (ne_of_gt hpos1) (ne_of_gt (mul_pos hpos2 hpos3))]
  rw [Real.log_mul (ne_of_gt hpos2) (ne_of_gt hpos3)]
  rw [Real.log_pow]
  rw [Real.log_div (ne_of_gt (Nat.cast_pos.mpr hn)) (ne_of_gt (Real.exp_pos 1))]
  rw [Real.log_exp]
  ring

-- ============================================================
-- PART 8: Connection to Other Theorems
-- ============================================================

/-!
### Connections to Other Results

**Wallis Product**: π/2 = ∏(4n²)/(4n² - 1)
The convergence of stirlingSeq uses this as a key ingredient.

**Gamma Function**: Γ(n+1) = n! for natural n
Stirling extends to Γ(x+1) ~ √(2πx)(x/e)^x for all x > 0.

**Central Limit Theorem**: Stirling's formula is used in deriving
the CLT via characteristic functions.

**de Moivre-Laplace**: The local CLT for binomial distributions
uses Stirling to approximate binomial coefficients.
-/

-- Export main results
#check @stirlingSeq_tendsto_sqrt_pi
#check @stirling_formula
#check @factorial_lower_bound
#check @factorial_div_approx_tendsto_one

end StirlingFormula
