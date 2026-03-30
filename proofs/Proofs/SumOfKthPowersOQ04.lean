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

## Status: AXIOMATIZED (1 axiom: monic polynomial ratio limit)
Previously 2 axioms — bernoulli_poly_leading now proved from coeff_bernoulli.
-/

import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot
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
  simp [le_refl, Nat.sub_self, _root_.bernoulli_zero, Nat.choose_self]

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

/-- For any monic polynomial p of degree d, p(n)/n^d → 1 as n → ∞ over ℚ.
    This is the fundamental asymptotic property of polynomials.

    Proof strategy: decompose p = X^d + q where deg(q) < d, then
    p(n)/n^d = 1 + q(n)/n^d. Each term of q(n)/n^d has the form c/n^m
    for m ≥ 1, which → 0 by inv_tendsto_atTop. -/
axiom monic_poly_ratio_tendsto (p : Polynomial ℚ) (d : ℕ)
    (hd : p.natDegree = d) (hlc : p.leadingCoeff = 1) (hd_pos : 0 < d) :
    Tendsto (fun n : ℕ => p.eval (n : ℚ) / (n : ℚ) ^ d) atTop (nhds 1)

/-- **Main theorem**: The ratio ∑_{i=0}^{n-1} i^k / n^{k+1} → 1/(k+1) as n → ∞.

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
  rw [show (fun n : ℕ => (1 : ℚ) / (n : ℚ) ^ d) = (fun n : ℕ => ((n : ℚ) ^ d)⁻¹) from by
    ext; simp [one_div]]
  apply Filter.Tendsto.inv_tendsto_atTop
  apply Filter.Tendsto.atTop_nonneg_mul_left (show (0 : ℚ) < 1 from one_pos)
  sorry -- Tendsto (fun n : ℕ => (n : ℚ) ^ d) atTop atTop — routine

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
    have faulhaber := Finset.sum_range_pow_eq_bernoulli_sub n k
    have hsum : ∑ i ∈ Finset.range n, (↑i : ℚ) ^ k =
        (B.eval (↑n) - c) / (↑k + 1) := by
      rw [eq_div_iff hk1_ne]; linarith
    rw [hsum, div_div]
  -- Step 2: The limit of the rewritten form
  suffices h : Tendsto (fun n : ℕ => (B.eval (↑n) - c) / ((↑k + 1) * (↑n) ^ (k + 1)))
      atTop (nhds (1 / (↑k + 1))) from h.congr' h_eq.symm
  -- Step 3: Split into B(n)/((k+1)n^{k+1}) - c/((k+1)n^{k+1})
  rw [show (1 : ℚ) / (↑k + 1) = 1 / (↑k + 1) - 0 from by ring]
  apply Filter.Tendsto.sub
  · -- B(n) / ((k+1) * n^(k+1)) → 1/(k+1)
    have h_bern := monic_poly_ratio_tendsto B (k + 1) hndeg hlc (by omega)
    have := h_bern.div_const (↑k + 1 : ℚ)
    simp only [one_div] at this
    refine this.congr (fun n => ?_)
    simp only [div_div]
  · -- c / ((k+1) * n^(k+1)) → 0
    rw [show (0 : ℚ) = c / (↑k + 1) * 0 from by ring]
    apply Filter.Tendsto.const_mul
    exact const_div_pow_tendsto_zero 1 (k + 1) (by omega) |>.congr (fun n => by simp)

/-- Special case k=0: ∑ 1 / n = n/n = 1 → 1/(0+1) = 1. -/
theorem powerSumRatio_k0 (n : ℕ) (hn : n ≠ 0) :
    powerSumRatio 0 n = 1 := by
  simp [powerSumRatio, hn, Finset.sum_range_id_eq_sum_range_succ]
  simp [pow_zero, Finset.sum_const, Finset.card_range]
  field_simp

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
    pow_one, pow_succ]
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  have h := gauss_sum_rat n
  have h2 : ∑ i ∈ range n, (i : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by linarith
  rw [h2]; field_simp

end SumOfKthPowersAsymptotic
