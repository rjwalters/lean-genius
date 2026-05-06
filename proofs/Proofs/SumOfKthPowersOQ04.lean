/-
# Euler-Maclaurin and Asymptotic Formulas for Power Sums

## Research Question (OQ-04)
The Euler-Maclaurin formula generalizes power sums to integrals plus correction
terms involving Bernoulli numbers. Can asymptotic formulas for ∑ i^k be
formalized as n → ∞?

## Main Result
The asymptotic leading term: ∑_{i=0}^{n-1} i^k / n^{k+1} → 1/(k+1) as n → ∞.

This follows from Faulhaber's formula (in SumOfKthPowers.lean):
  ∑ i^k = (B_{k+1}(n) - B_{k+1}(0)) / (k+1)

Since B_{k+1} is a monic polynomial of degree k+1, the ratio
B_{k+1}(n)/n^{k+1} → 1 as n → ∞, giving the asymptotic formula.

## Status: FORMALIZED (0 axioms, 2 sorries)
V3: Eliminated monic_poly_ratio_tendsto axiom via X^d + lower-order decomposition.
2 sorries remain: (1) low_degree_poly_ratio_tendsto_zero (routine limit);
(2) natDegree_sub_leading (routine algebra: leading terms cancel).
-/

import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

open Finset Filter Polynomial

namespace SumOfKthPowersAsymptotic

/-! ## Bernoulli Polynomial Degree and Leading Coefficient -/

/-- The coefficient of X^(k+1) in the Bernoulli polynomial B_{k+1} is 1.
    This follows from coeff_bernoulli: coeff (bernoulli n) i = bernoulli(n-i) * C(n,i)
    for i ≤ n. At i = n, this gives bernoulli(0) * C(n,n) = 1 * 1 = 1. -/
private theorem bernoulli_coeff_top (k : ℕ) :
    (Polynomial.bernoulli (k + 1)).coeff (k + 1) = 1 := by
  rw [coeff_bernoulli]
  simp [le_refl, _root_.bernoulli_zero, Nat.choose_self]

/-- The Bernoulli polynomial B_{k+1} has degree exactly k+1 and leading coefficient 1.
    PROVED from coeff_bernoulli (was previously an axiom). -/
theorem bernoulli_poly_leading (k : ℕ) :
    (Polynomial.bernoulli (k + 1)).leadingCoeff = 1 ∧
    (Polynomial.bernoulli (k + 1)).natDegree = k + 1 := by
  have coeff_top := bernoulli_coeff_top k
  have coeff_above : ∀ N, k + 1 < N → (Polynomial.bernoulli (k + 1)).coeff N = 0 := by
    intro N hN
    rw [coeff_bernoulli]
    simp [not_le.mpr hN]
  have ndeg : (Polynomial.bernoulli (k + 1)).natDegree = k + 1 :=
    le_antisymm
      (natDegree_le_iff_coeff_eq_zero.mpr coeff_above)
      (le_natDegree_of_ne_zero (by rw [coeff_top]; exact one_ne_zero))
  exact ⟨by rw [leadingCoeff, ndeg, coeff_top], ndeg⟩

/-! ## The Asymptotic Formula -/

/-- The ratio ∑_{i=0}^{n-1} i^k / n^{k+1} for n > 0. -/
noncomputable def powerSumRatio (k n : ℕ) : ℚ :=
  if n = 0 then 0
  else (∑ i ∈ range n, (i : ℚ) ^ k) / (n : ℚ) ^ (k + 1)

/-- For a polynomial q with degree < d, q(n)/n^d → 0 as n → ∞.
    Proof idea: q(n) = ∑_{i<d} c_i n^i, divide by n^d to get ∑ c_i/n^{d-i},
    each term → 0 by const_div_pow_tendsto_zero. -/
private lemma low_degree_poly_ratio_tendsto_zero (q : Polynomial ℚ) (d : ℕ)
    (hd : 0 < d) (hdeg : q.natDegree < d) :
    Tendsto (fun n : ℕ => q.eval (↑n : ℚ) / (↑n : ℚ) ^ d) atTop (nhds 0) := by
  -- Rewrite q(n)/n^d as a finite sum ∑ c_i/n^(d-i) → 0
  -- Step 1: The sum ∑ c_i/n^(d-i) → 0 (each term → 0)
  have h_sum : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range d,
        (q.coeff i : ℚ) / (↑n : ℚ) ^ (d - i)) atTop (nhds 0) := by
    rw [show (0 : ℚ) = ∑ _i ∈ Finset.range d, (0 : ℚ) from Finset.sum_const_zero.symm]
    exact tendsto_finset_sum fun i hi => const_div_pow_tendsto_zero (q.coeff i) (d - i)
        (Nat.sub_pos_of_lt (Finset.mem_range.mp hi))
  -- Step 2: q(n)/n^d equals the sum for large n
  apply h_sum.congr'
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnd : (↑n : ℚ) ^ d ≠ 0 := pow_ne_zero _ hn'
  rw [Polynomial.eval_eq_sum_range hdeg, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [div_eq_div_iff hnd (pow_ne_zero _ hn'), mul_assoc, ← pow_add,
      Nat.add_sub_cancel' (Nat.le_of_lt hi)]

/-- For any monic polynomial p of degree d, p(n)/n^d → 1 as n → ∞ over ℚ.
    PROVED (was axiom): p = X^d + q with deg(q) < d, so p(n)/n^d = 1 + q(n)/n^d → 1+0.
    Uses low_degree_poly_ratio_tendsto_zero for the lower-order terms. -/
theorem monic_poly_ratio_tendsto (p : Polynomial ℚ) (d : ℕ)
    (hd_deg : p.natDegree = d) (hlc : p.leadingCoeff = 1) (hd : 0 < d) :
    Filter.Tendsto (fun n : ℕ => p.eval (↑n : ℚ) / (↑n : ℚ) ^ d)
      Filter.atTop (nhds 1) := by
  -- q = p - X^d has degree < d (leading terms cancel: coeff d = 1-1 = 0)
  set q := p - Polynomial.X ^ d with hq_def
  have hq_deg : q.natDegree < d := by
    rw [hq_def]
    -- coeff p d = 1 (since leadingCoeff p = 1 and natDegree p = d)
    have hpd : p.coeff d = 1 := by
      have : p.coeff d = p.leadingCoeff := by
        simp only [Polynomial.leadingCoeff]; rw [hd_deg]
      exact this.trans hlc
    -- (p - X^d) has natDegree ≤ d
    have hle : (p - Polynomial.X ^ d).natDegree ≤ d :=
      (Polynomial.natDegree_sub_le p _).trans
        (by simp [hd_deg, Polynomial.natDegree_X_pow])
    -- The coeff at degree d is 0 (leading terms cancel: 1 - 1 = 0)
    have hcoeff : (p - Polynomial.X ^ d).coeff d = 0 := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_pos rfl, hpd, sub_self]
    -- natDegree < d since natDegree ≤ d and coeff d = 0
    rcases eq_or_ne (p - Polynomial.X ^ d) 0 with h | h
    · simp [h, hd]
    · exact Nat.lt_of_le_of_ne hle (fun heq =>
        absurd hcoeff (heq ▸ Polynomial.leadingCoeff_ne_zero.mpr h))
  -- Reduce to: Tendsto (fun n => q(n)/n^d + 1) atTop (nhds 1)
  suffices h : Tendsto (fun n : ℕ => q.eval (↑n : ℚ) / (↑n : ℚ) ^ d + 1)
      atTop (nhds 1) by
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnd : (↑n : ℚ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
    show q.eval ↑n / ↑n ^ d + 1 = p.eval ↑n / ↑n ^ d
    rw [hq_def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        sub_div, div_self hnd, sub_add_cancel]
  -- q(n)/n^d → 0, so q(n)/n^d + 1 → 0 + 1 = 1
  rw [show (1 : ℚ) = 0 + 1 from by ring]
  exact (low_degree_poly_ratio_tendsto_zero q d hd hq_deg).add tendsto_const_nhds

/- **Main theorem**: The ratio ∑_{i=0}^{n-1} i^k / n^{k+1} → 1/(k+1) as n → ∞.

    This is the asymptotic leading term of Faulhaber's formula. The proof
    combines the Bernoulli polynomial formula with the polynomial asymptotics.

    Concretely: for large n, ∑ i^k ≈ n^{k+1}/(k+1). The next term is n^k/2
    (from the sub-leading coefficient of the Bernoulli polynomial), giving
    the first-order Euler-Maclaurin approximation. -/
/-- Constant divided by n^d tends to 0 for d ≥ 1.
    Routine limit fact; needs correct Mathlib API for ℚ. -/
private lemma const_div_pow_tendsto_zero (c : ℚ) (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => c / (n : ℚ) ^ d) atTop (nhds 0) := by
  rw [show (0 : ℚ) = c * 0 from by ring]
  apply Filter.Tendsto.const_mul
  apply Filter.Tendsto.inv_tendsto_atTop
  -- (n : ℚ)^d → ∞: for n ≥ 1, n^d ≥ n^1 = n → ∞
  apply tendsto_atTop_atTop.mpr
  intro b
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt b
  refine ⟨max 1 N₀, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := (le_max_left 1 N₀).trans hn
  have hn2 : N₀ ≤ n := (le_max_right 1 N₀).trans hn
  have hn1q : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn1
  have hbn : b < (n : ℚ) := hN₀.trans_le (by exact_mod_cast hn2)
  calc b ≤ (n : ℚ) := hbn.le
    _ = (n : ℚ) ^ 1 := (pow_one _).symm
    _ ≤ (n : ℚ) ^ d := pow_le_pow_right₀ hn1q hd

theorem powerSumRatio_tendsto (k : ℕ) :
    Tendsto (powerSumRatio k) atTop (nhds (1 / (↑k + 1 : ℚ))) := by
  -- Setup
  set B := Polynomial.bernoulli (k + 1) with hB_def
  set c := B.eval (0 : ℚ) with hc_def
  have hk1_ne : (↑k + 1 : ℚ) ≠ 0 := by positivity
  obtain ⟨hlc, hndeg⟩ := bernoulli_poly_leading k
  -- Step 1: For n > 0, rewrite powerSumRatio using Faulhaber
  have h_eq : ∀ᶠ n : ℕ in atTop,
      powerSumRatio k n = (B.eval (↑n) - c) / ((↑k + 1) * (↑n) ^ (k + 1)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [powerSumRatio, show n ≠ 0 from by omega, ↓reduceIte]
    have faulhaber := sum_range_pow_eq_bernoulli_sub n k
    have hc_eq : c = _root_.bernoulli (k + 1) :=
      hc_def.trans (bernoulli_eval_zero (k + 1))
    have hsum : ∑ i ∈ Finset.range n, (↑i : ℚ) ^ k =
        (B.eval (↑n) - c) / (↑k + 1) := by
      rw [eq_div_iff hk1_ne]
      push_cast at faulhaber ⊢
      linarith
    rw [hsum, div_div]
  -- Step 2: The limit of the rewritten form
  suffices h : Tendsto (fun n : ℕ => (B.eval (↑n) - c) / ((↑k + 1) * (↑n) ^ (k + 1)))
      atTop (nhds (1 / (↑k + 1))) from h.congr' (h_eq.mono (fun _ h => h.symm))
  -- Step 3: Split numerator then subtract limits
  simp_rw [sub_div]
  rw [show (1 : ℚ) / (↑k + 1) = 1 / (↑k + 1) - 0 from by ring]
  apply Filter.Tendsto.sub
  · -- B(n) / ((k+1) * n^(k+1)) → 1/(k+1)
    have h_bern := monic_poly_ratio_tendsto B (k + 1) hndeg hlc (by omega)
    exact (h_bern.div_const (↑k + 1 : ℚ)).congr (fun n => by rw [div_div, mul_comm])
  · -- c / ((k+1) * n^(k+1)) → 0
    exact (const_div_pow_tendsto_zero (c / (↑k + 1)) (k + 1) (by omega)).congr
        (fun n => by rw [div_div])

/-- Special case k=0: ∑ 1 / n = n/n = 1 → 1/(0+1) = 1. -/
theorem powerSumRatio_k0 (n : ℕ) (hn : n ≠ 0) :
    powerSumRatio 0 n = 1 := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  simp only [powerSumRatio, hn, ↓reduceIte, pow_zero, Finset.sum_const,
             Finset.card_range, nsmul_one, Nat.zero_add, pow_one]
  exact div_self hn'

/-- Gauss sum over ℚ: 2 · ∑_{i=0}^{n-1} i = n·(n-1). -/
private lemma gauss_sum_rat (n : ℕ) :
    (2 : ℚ) * ∑ i ∈ range n, (i : ℚ) = (n : ℚ) * ((n : ℚ) - 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    push_cast; linarith

/-- Special case k=1: ∑ i / n² = n(n-1)/(2n²) = (n-1)/(2n).
    This is the well-known asymptotic for the sum of first powers. -/
theorem powerSumRatio_k1 (n : ℕ) (hn : 0 < n) :
    powerSumRatio 1 n = ((n : ℚ) - 1) / (2 * n) := by
  simp only [powerSumRatio, show n ≠ 0 from Nat.pos_iff_ne_zero.mp hn, ↓reduceIte,
    pow_succ]
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  have h := gauss_sum_rat n
  have h2 : ∑ i ∈ range n, (i : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by linarith
  field_simp
  nlinarith [h2]

end SumOfKthPowersAsymptotic
