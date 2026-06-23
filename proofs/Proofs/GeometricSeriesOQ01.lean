import Mathlib.Algebra.GeomSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-
# Geometric Series at the Boundary: |r| = 1

## What This Proves
The behavior of the geometric series ∑ rⁿ at the critical boundary |r| = 1,
where the series transitions from convergent to divergent:

1. **r = 1**: Partial sums Sₙ = n diverge to infinity
2. **r = -1 (Grandi's series)**: Partial sums oscillate: S₂ₘ = 0, S₂ₘ₊₁ = 1
3. **|r| ≥ 1 implies not summable**: |rⁿ| ≥ 1, so terms don't tend to zero
4. **Cesàro summability**: The Cesàro mean of Grandi's series converges to 1/2

## Historical Context
Grandi's series 1 - 1 + 1 - 1 + ⋯ was studied by Guido Grandi (1703). Its
"sum" was debated for over a century: Euler assigned it the value 1/2 via
regularization. Cesàro (1890) formalized this by averaging partial sums —
giving the rigorous result σₙ → 1/2. This was an early example of summability
theory, which extends convergence to assign finite values to divergent series.

The boundary |r| = 1 is where the radius of convergence of the geometric
series meets the unit circle. Inside (|r| < 1), the series converges to
1/(1-r). On the boundary, the behavior is more subtle and depends on r.

## Approach
- **Foundation (from Mathlib):** Finite geometric sum formula `mul_neg_geom_sum`.
- **Original Contributions:** Explicit boundary behavior analysis, Cesàro
  summability with convergence proof via squeeze theorem.
- **Proof Techniques:** Parity case analysis, subsequence extraction, squeeze.
-/

namespace GeometricSeriesOQ01

open Finset BigOperators Filter

-- ============================================================
-- PART 1: Divergence at r = 1
-- ============================================================

/-- At r = 1, the geometric partial sum is simply n. -/
theorem geom_partial_sum_one (n : ℕ) :
    ∑ k ∈ range n, (1 : ℝ) ^ k = (n : ℝ) := by
  simp [one_pow]

/-- The partial sums at r = 1 diverge to infinity. -/
theorem geom_sum_one_diverges :
    Tendsto (fun n => ∑ k ∈ range n, (1 : ℝ) ^ k) atTop atTop := by
  simp only [one_pow, sum_const, card_range, Nat.smul_one_eq_cast]
  exact tendsto_natCast_atTop_atTop

/-- The constant sequence 1, 1, 1, ... is not summable. -/
theorem not_summable_one : ¬Summable (fun _ : ℕ => (1 : ℝ)) := by
  intro h
  have := h.tendsto_atTop_zero
  simp only [tendsto_const_nhds_iff] at this
  exact one_ne_zero this

-- ============================================================
-- PART 2: Oscillation at r = -1 (Grandi's Series)
-- ============================================================

/-- The finite geometric sum formula applied at r = -1:
    2 · Sₙ = 1 - (-1)ⁿ, where Sₙ = ∑_{k=0}^{n-1} (-1)^k. -/
theorem grandi_double_sum (n : ℕ) :
    2 * ∑ k ∈ range n, (-1 : ℝ) ^ k = 1 - (-1) ^ n := by
  have h := mul_neg_geom_sum (-1 : ℝ) n
  linarith

/-- Even partial sums of Grandi's series equal 0. -/
theorem grandi_even (m : ℕ) :
    ∑ k ∈ range (2 * m), (-1 : ℝ) ^ k = 0 := by
  have h := grandi_double_sum (2 * m)
  have : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
  linarith

/-- Odd partial sums of Grandi's series equal 1. -/
theorem grandi_odd (m : ℕ) :
    ∑ k ∈ range (2 * m + 1), (-1 : ℝ) ^ k = 1 := by
  have h := grandi_double_sum (2 * m + 1)
  have : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
    rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  linarith

/-- Grandi's series is not summable: the even subsequence (-1)^(2m) = 1
    doesn't tend to zero. -/
theorem not_summable_grandi : ¬Summable (fun n : ℕ => (-1 : ℝ) ^ n) := by
  intro h
  have htend := h.tendsto_atTop_zero
  -- |(-1)^n| = 1 for all n, but terms must tend to 0
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend (1 / 2) (by norm_num)
  have h1 := hN N le_rfl
  rw [dist_zero_right] at h1
  have h2 : |(-1 : ℝ) ^ N| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  simp only [Real.norm_eq_abs] at h1
  linarith

-- ============================================================
-- PART 3: General |r| ≥ 1 Implies Not Summable
-- ============================================================

/-- For |r| ≥ 1, the geometric series is not summable.
    The terms |rⁿ| = |r|ⁿ ≥ 1 don't tend to zero. -/
theorem not_summable_geom_of_one_le_norm {r : ℝ} (hr : 1 ≤ |r|) :
    ¬Summable (fun n : ℕ => r ^ n) := by
  intro h
  have htend := h.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend (1 / 2) (by norm_num)
  have h1 := hN N le_rfl
  rw [dist_zero_right] at h1
  have h2 : 1 ≤ |r ^ N| := by rw [abs_pow]; exact one_le_pow₀ hr
  simp only [Real.norm_eq_abs] at h1
  linarith

/-- Specialization: the series ∑ rⁿ diverges when |r| = 1. -/
theorem not_summable_geom_of_norm_eq_one {r : ℝ} (hr : |r| = 1) :
    ¬Summable (fun n : ℕ => r ^ n) :=
  not_summable_geom_of_one_le_norm (le_of_eq hr.symm)

-- ============================================================
-- PART 4: Cesàro Summability of Grandi's Series
-- ============================================================

/-- The Cesàro mean of Grandi's series:
    σₙ = (1/n) · (S₁ + S₂ + ⋯ + Sₙ) where Sₖ = ∑_{j<k} (-1)^j -/
noncomputable def grandiCesaro (n : ℕ) : ℝ :=
  if n = 0 then 0
  else (Finset.sum (range n) fun k => ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j) / n

/-- The sum of the first n Grandi partial sums equals ⌈n/2⌉.
    Since S_{odd} = 1 and S_{even} = 0, the sum counts the odd indices. -/
theorem sum_grandi_partial_sums (n : ℕ) :
    (∑ k ∈ range n, (∑ j ∈ range (k + 1), (-1 : ℝ) ^ j)) = ((n + 1) / 2 : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- n = 2m: adding S_{2m+1} = 1
      subst hm
      have hS : ∑ j ∈ range (m + m + 1), (-1 : ℝ) ^ j = 1 := by
        have h_eq : m + m + 1 = 2 * m + 1 := by omega
        rw [h_eq]; exact grandi_odd m
      rw [hS]; push_cast
      have h1 : (m + m + 1) / 2 = m := by omega
      have h2 : (m + m + 1 + 1) / 2 = m + 1 := by omega
      simp [h1, h2]
    · -- n = 2m+1: adding S_{2(m+1)} = 0
      subst hm
      have hS : ∑ j ∈ range (2 * m + 1 + 1), (-1 : ℝ) ^ j = 0 := by
        have h_eq : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
        rw [h_eq]; exact grandi_even (m + 1)
      rw [hS, add_zero]; push_cast
      have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      have h2 : (2 * m + 1 + 1 + 1) / 2 = m + 1 := by omega
      simp [h1, h2]

/-- The Cesàro mean equals ⌈n/2⌉ / n for n ≥ 1. -/
theorem grandiCesaro_eq {n : ℕ} (hn : 0 < n) :
    grandiCesaro n = ((n + 1) / 2 : ℕ) / (n : ℝ) := by
  simp only [grandiCesaro, if_neg (by omega : n ≠ 0), sum_grandi_partial_sums]

/-- Key bound: |σₙ - 1/2| ≤ 1/(2n) for n ≥ 1.

    Proof: Express σₙ - 1/2 = (2·⌈n/2⌉ - n) / (2n). Since n ≤ 2·⌈n/2⌉ ≤ n+1,
    we have |2·⌈n/2⌉ - n| ≤ 1, giving |σₙ - 1/2| ≤ 1/(2n). -/
theorem grandiCesaro_bound {n : ℕ} (hn : 0 < n) :
    |grandiCesaro n - 1 / 2| ≤ 1 / (2 * n) := by
  rw [grandiCesaro_eq hn]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  -- Express the difference as (2c - n) / (2n) where c = (n+1)/2
  set c := (n + 1) / 2 with hc_def
  -- |2c - n| ≤ 1 because n ≤ 2c ≤ n + 1
  have hlower : n ≤ 2 * c := by omega
  have hupper : 2 * c ≤ n + 1 := by omega
  have hlower_r : (↑n : ℝ) ≤ 2 * ↑c := by exact_mod_cast hlower
  have hupper_r : 2 * (↑c : ℝ) ≤ ↑n + 1 := by exact_mod_cast hupper
  -- σ - 1/2 = (2c - n)/(2n), so |σ - 1/2| = |2c - n|/(2n) ≤ 1/(2n)
  have hkey : (↑c : ℝ) / ↑n - 1 / 2 = (2 * ↑c - ↑n) / (2 * ↑n) := by
    field_simp
  rw [hkey, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * ↑n)]
  apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ 2 * ↑n)
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **Cesàro's Theorem for Grandi's Series**: The Cesàro mean σₙ → 1/2.

    While the series 1 - 1 + 1 - 1 + ⋯ does not converge in the usual sense,
    the averages of its partial sums converge to 1/2. This is the simplest
    nontrivial example of Cesàro summability. -/
theorem grandiCesaro_tendsto :
    Tendsto grandiCesaro atTop (nhds (1 / 2)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Need N such that ∀ n ≥ N, |σ_n - 1/2| < ε
  -- We have |σ_n - 1/2| ≤ 1/(2n), so need 1/(2n) < ε, i.e., n > 1/(2ε)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (2 * ε))
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 0 < n := by omega
  rw [Real.dist_eq]
  calc |grandiCesaro n - 1 / 2|
      ≤ 1 / (2 * n) := grandiCesaro_bound hn1
    _ < ε := by
        have hN_le : (N : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
        have hbound : 1 / (2 * ε) < (n : ℝ) := lt_of_lt_of_le hN hN_le
        rw [div_lt_iff₀ (show (0:ℝ) < 2 * ↑n from by positivity)]
        rw [div_lt_iff₀ (show (0:ℝ) < 2 * ε from by positivity)] at hbound
        nlinarith

-- ============================================================
-- PART 5: Examples
-- ============================================================

-- Divergence at r = 1
example : ∑ k ∈ range 10, (1 : ℝ) ^ k = 10 := by simp [one_pow]

-- Grandi's series: even partial sum = 0, odd = 1
example : ∑ k ∈ range 6, (-1 : ℝ) ^ k = 0 := grandi_even 3
example : ∑ k ∈ range 7, (-1 : ℝ) ^ k = 1 := grandi_odd 3

/-
The complete picture at the boundary |r| = 1:

  r     │ Partial sums Sₙ      │ Summable? │ Cesàro sum
  ──────┼───────────────────────┼───────────┼───────────
  1     │ n → ∞                 │ No        │ Diverges
  -1    │ 0, 1, 0, 1, ...      │ No        │ 1/2
  i     │ bounded, not converge │ No        │ 1/2
  e^iθ  │ bounded ≤ 2/|1-e^iθ| │ No        │ 1/(1-e^iθ)

The boundary is a phase transition: inside the disk (|r| < 1) everything
converges; on the boundary, classical convergence fails but Cesàro (and
Abel) summability can still assign meaningful values.
-/

#check @geom_partial_sum_one
#check @grandi_even
#check @grandi_odd
#check @not_summable_geom_of_one_le_norm
#check @grandiCesaro_tendsto

end GeometricSeriesOQ01
