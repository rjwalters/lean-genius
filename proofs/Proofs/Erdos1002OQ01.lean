/-
Erdős Problem #1002 — OQ-01: Proving Axioms

Eliminates two axioms from Erdos1002Problem.lean:
1. cauchy_is_distribution: The Cauchy CDF is a valid distribution function.
2. innerSum_periodic_rational: Inner sum periodicity for rational α.

Both are standard results proved from Mathlib.
-/

import Mathlib

set_option maxHeartbeats 800000

open Real Filter

namespace Erdos1002OQ01

/-! ## Definitions (mirrored from Erdos1002Problem.lean) -/

/-- A distribution function: monotone with correct limits at ±∞. -/
def IsDistributionFunction (g : ℝ → ℝ) : Prop :=
  Monotone g ∧ Tendsto g atBot (nhds 0) ∧ Tendsto g atTop (nhds 1)

/-- The Cauchy CDF: g(c) = (1/π) arctan(ρc) + 1/2. -/
noncomputable def cauchyDistribution (ρ : ℝ) (c : ℝ) : ℝ :=
  1 / π * arctan (ρ * c) + 1 / 2

/-- Deviation from midpoint: 1/2 - {x}. -/
noncomputable def deviation (x : ℝ) : ℝ :=
  1 / 2 - Int.fract x

/-- Inner sum: S(α, n) = Σ_{k=1}^n (1/2 - {αk}). -/
noncomputable def innerSum (α : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, deviation (α * (↑k + 1))

/-! ## Part I: Cauchy Distribution is a Valid Distribution Function -/

private theorem cauchy_monotone (ρ : ℝ) (hρ : ρ > 0) :
    Monotone (cauchyDistribution ρ) := by
  intro a b hab
  simp only [cauchyDistribution]
  gcongr
  exact arctan_strictMono.monotone (mul_le_mul_of_nonneg_left hab hρ.le)

private theorem tendsto_mul_atTop (ρ : ℝ) (hρ : ρ > 0) :
    Tendsto (fun c => ρ * c) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b / ρ, fun c hc => ?_⟩
  have h1 : ρ * (b / ρ) ≤ ρ * c := mul_le_mul_of_nonneg_left hc hρ.le
  have h2 : ρ * (b / ρ) = b := by field_simp
  linarith

private theorem tendsto_mul_atBot (ρ : ℝ) (hρ : ρ > 0) :
    Tendsto (fun c => ρ * c) atBot atBot := by
  rw [Filter.tendsto_atBot_atBot]
  intro b
  refine ⟨b / ρ, fun c hc => ?_⟩
  have h1 : ρ * c ≤ ρ * (b / ρ) := mul_le_mul_of_nonneg_left hc hρ.le
  have h2 : ρ * (b / ρ) = b := by field_simp
  linarith

private theorem cauchy_tendsto_one (ρ : ℝ) (hρ : ρ > 0) :
    Tendsto (cauchyDistribution ρ) atTop (nhds 1) := by
  simp only [cauchyDistribution]
  have h_arc : Tendsto (fun c => arctan (ρ * c)) atTop (nhds (π / 2)) :=
    tendsto_arctan_atTop.comp (tendsto_mul_atTop ρ hρ)
  have h_lim : Tendsto (fun c => 1 / π * arctan (ρ * c) + 1 / 2) atTop
      (nhds (1 / π * (π / 2) + 1 / 2)) :=
    (tendsto_const_nhds.mul h_arc).add tendsto_const_nhds
  convert h_lim using 1
  field_simp

private theorem cauchy_tendsto_zero (ρ : ℝ) (hρ : ρ > 0) :
    Tendsto (cauchyDistribution ρ) atBot (nhds 0) := by
  simp only [cauchyDistribution]
  have h_arc : Tendsto (fun c => arctan (ρ * c)) atBot (nhds (-(π / 2))) :=
    tendsto_arctan_atBot.comp (tendsto_mul_atBot ρ hρ)
  have h_lim : Tendsto (fun c => 1 / π * arctan (ρ * c) + 1 / 2) atBot
      (nhds (1 / π * (-(π / 2)) + 1 / 2)) :=
    (tendsto_const_nhds.mul h_arc).add tendsto_const_nhds
  convert h_lim using 1
  field_simp

/-- **PROVED** (was axiom in Erdos1002Problem.lean):
    The Cauchy CDF is a valid distribution function. -/
theorem cauchy_is_distribution (ρ : ℝ) (hρ : ρ > 0) :
    IsDistributionFunction (cauchyDistribution ρ) :=
  ⟨cauchy_monotone ρ hρ, cauchy_tendsto_zero ρ hρ, cauchy_tendsto_one ρ hρ⟩

/-! ## Part II: Periodicity of Inner Sum for Rational α -/

/-- deviation is invariant under integer shifts: deviation(x + n) = deviation(x). -/
private theorem deviation_add_int (x : ℝ) (n : ℤ) :
    deviation (x + ↑n) = deviation x := by
  unfold deviation
  congr 1
  rw [Int.fract, Int.fract, Int.floor_add_intCast]
  push_cast; ring

/-- The function k ↦ deviation(p/q · (k+1)) has period q. -/
private theorem deviation_rational_periodic (p : ℤ) (q : ℕ) (hq : q ≥ 1) (k : ℕ) :
    deviation (↑p / ↑q * (↑(k + q) + 1)) = deviation (↑p / ↑q * (↑k + 1)) := by
  have hq_ne : (↑q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  rw [show (↑k : ℝ) + ↑q + 1 = (↑k + 1) + ↑q from by ring, mul_add,
      show (↑p : ℝ) / ↑q * ↑q = ↑p from by field_simp]
  exact deviation_add_int _ p

/-- Summing a periodic function over any q consecutive values gives the same result. -/
private theorem cyclic_sum_periodic (g : ℕ → ℝ) (q : ℕ) (hper : ∀ k, g (k + q) = g k)
    (n : ℕ) : ∑ k in Finset.range q, g (n + k) = ∑ k in Finset.range q, g k := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h_rw : ∀ k, g (m + 1 + k) = g (m + (k + 1)) := fun k => by congr 1; omega
    simp_rw [h_rw]
    -- Use sum_range_succ and sum_range_succ' for f(k) = g(m+k) to show
    -- ∑ range q, f(k+1) = ∑ range q, f(k) when f(q) = f(0)
    have hr := Finset.sum_range_succ (fun k => g (m + k)) q
    have hr' := Finset.sum_range_succ' (fun k => g (m + k)) q
    have hper_m : g (m + q) = g m := hper m
    -- hr:  ∑ range (q+1), g(m+k) = (∑ range q, g(m+k)) + g(m+q)
    -- hr': ∑ range (q+1), g(m+k) = (∑ range q, g(m+(k+1))) + g(m+0)
    -- From hr, hr', hper_m: ∑ range q, g(m+(k+1)) = ∑ range q, g(m+k) = ∑ range q, g(k)
    linarith

/-- **PROVED** (was axiom in Erdos1002Problem.lean):
    For rational α = p/q, the inner sum satisfies S(α, n+q) = S(α, n) + S(α, q). -/
theorem innerSum_periodic_rational (p : ℤ) (q : ℕ) (hq : q ≥ 1) (hcop : Int.gcd p q = 1) :
    ∀ n : ℕ, innerSum (↑p / ↑q) (n + q) = innerSum (↑p / ↑q) n + innerSum (↑p / ↑q) q := by
  intro n
  simp only [innerSum]
  rw [Finset.sum_range_add]
  congr 1
  exact cyclic_sum_periodic (fun k => deviation (↑p / ↑q * (↑k + 1))) q
    (deviation_rational_periodic p q hq) n

end Erdos1002OQ01
