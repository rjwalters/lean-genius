import Mathlib.Analysis.MeanInequalities

/-
# Generalized (n-fold) Hölder inequality for finite sums

This file proves the **generalized Hölder inequality** for finite sums with `n` exponents,
filling a gap in Mathlib, which provides only the two-exponent discrete Hölder inequality
`NNReal.inner_le_Lp_mul_Lq` / `Real.inner_le_Lp_mul_Lq_of_nonneg`.

Given finitely many nonnegative functions `f j : ι → ℝ` (`j ∈ t`) and positive exponents
`p j` with `∑ j, (p j)⁻¹ = 1`, we prove
`∑ i ∈ s, ∏ j ∈ t, f j i ≤ ∏ j ∈ t, (∑ i ∈ s, f j i ^ p j) ^ (p j)⁻¹`.

The two-function case `t = {a, b}` with `1 / p a + 1 / p b = 1` recovers the classical Hölder
inequality `∑ᵢ uᵢ vᵢ ≤ (∑ᵢ uᵢ ^ p) ^ (1/p) · (∑ᵢ vᵢ ^ q) ^ (1/q)`.

## Main results

* `young_product` : the pointwise `n`-variable Young product inequality
  `∏ j, a j ≤ ∑ j, (p j)⁻¹ * a j ^ p j`, a direct consequence of the weighted AM–GM
  inequality `Real.geom_mean_le_arith_mean_weighted`.
* `generalized_holder` : the generalized Hölder inequality for finite sums.
* `inner_le_holder_two` : the two-function specialization, the shape of the classical discrete
  Hölder inequality.

## Strategy

`young_product` follows from weighted AM–GM with weights `w j = (p j)⁻¹` and data
`z j = a j ^ p j`, using the telescoping identity `(a j ^ p j) ^ (p j)⁻¹ = a j`.

`generalized_holder` follows by the standard normalization argument: divide each `f j` by its
`Lᵖ`-norm `C j = (∑ i, f j i ^ p j) ^ (p j)⁻¹`, apply `young_product` pointwise to the
normalized functions, and sum.  The `C j = 0` columns are handled separately (the left-hand side
is then `0`).
-/

open Finset

namespace JensenHolder

variable {ι κ : Type*}

/-- **`n`-variable Young product inequality.** For nonnegative reals `a j` and positive exponents
`p j` whose reciprocals sum to `1`, the product `∏ a j` is bounded by the weighted sum of
`p j`-th powers `∑ (p j)⁻¹ * a j ^ p j`.  This is the pointwise tool behind the generalized
Hölder inequality. -/
theorem young_product (t : Finset κ) (a p : κ → ℝ)
    (ha : ∀ j ∈ t, 0 ≤ a j) (hp : ∀ j ∈ t, 0 < p j)
    (hsum : ∑ j ∈ t, (p j)⁻¹ = 1) :
    ∏ j ∈ t, a j ≤ ∑ j ∈ t, (p j)⁻¹ * a j ^ p j :=
  calc
    ∏ j ∈ t, a j = ∏ j ∈ t, (a j ^ p j) ^ (p j)⁻¹ := by
        refine prod_congr rfl fun j hj => ?_
        rw [← Real.rpow_mul (ha j hj), mul_inv_cancel₀ (hp j hj).ne', Real.rpow_one]
    _ ≤ ∑ j ∈ t, (p j)⁻¹ * a j ^ p j :=
        Real.geom_mean_le_arith_mean_weighted t (fun j => (p j)⁻¹) (fun j => a j ^ p j)
          (fun j hj => inv_nonneg.2 (hp j hj).le) hsum
          (fun j hj => Real.rpow_nonneg (ha j hj) _)

/-- **Generalized (n-fold) Hölder inequality for finite sums.** For nonnegative functions
`f j : ι → ℝ` indexed by `j ∈ t` and positive exponents `p j` whose reciprocals sum to `1`,
the sum of the products is bounded by the product of the `Lᵖ`-norms:
`∑ i ∈ s, ∏ j ∈ t, f j i ≤ ∏ j ∈ t, (∑ i ∈ s, f j i ^ p j) ^ (p j)⁻¹`. -/
theorem generalized_holder (s : Finset ι) (t : Finset κ) (f : κ → ι → ℝ) (p : κ → ℝ)
    (hf : ∀ j ∈ t, ∀ i ∈ s, 0 ≤ f j i) (hp : ∀ j ∈ t, 0 < p j)
    (hsum : ∑ j ∈ t, (p j)⁻¹ = 1) :
    ∑ i ∈ s, ∏ j ∈ t, f j i ≤ ∏ j ∈ t, (∑ i ∈ s, f j i ^ p j) ^ (p j)⁻¹ := by
  have hNnonneg : ∀ j ∈ t, 0 ≤ ∑ i ∈ s, f j i ^ p j := fun j hj =>
    sum_nonneg fun i hi => Real.rpow_nonneg (hf j hj i hi) _
  by_cases hzero : ∃ j ∈ t, (∑ i ∈ s, f j i ^ p j) = 0
  · -- a column `j₀` is identically zero ⇒ the left-hand side is `0`.
    obtain ⟨j₀, hj₀, hNj₀⟩ := hzero
    have hfzero : ∀ i ∈ s, f j₀ i = 0 := by
      intro i hi
      have hterm : f j₀ i ^ p j₀ = 0 :=
        (sum_eq_zero_iff_of_nonneg
          (fun i hi => Real.rpow_nonneg (hf j₀ hj₀ i hi) _)).1 hNj₀ i hi
      exact ((Real.rpow_eq_zero_iff_of_nonneg (hf j₀ hj₀ i hi)).1 hterm).1
    have hLHS : ∑ i ∈ s, ∏ j ∈ t, f j i = 0 :=
      sum_eq_zero fun i hi => prod_eq_zero hj₀ (hfzero i hi)
    rw [hLHS]
    exact prod_nonneg fun j hj => Real.rpow_nonneg (hNnonneg j hj) _
  · -- every column is strictly positive: normalize and apply `young_product`.
    push_neg at hzero
    have hNpos : ∀ j ∈ t, 0 < ∑ i ∈ s, f j i ^ p j := fun j hj =>
      (hNnonneg j hj).lt_of_ne (Ne.symm (hzero j hj))
    set C : κ → ℝ := fun j => (∑ i ∈ s, f j i ^ p j) ^ (p j)⁻¹ with hCdef
    have hCpos : ∀ j ∈ t, 0 < C j := fun j hj => Real.rpow_pos_of_pos (hNpos j hj) _
    have hCp : ∀ j ∈ t, C j ^ p j = ∑ i ∈ s, f j i ^ p j := by
      intro j hj
      show ((∑ i ∈ s, f j i ^ p j) ^ (p j)⁻¹) ^ p j = ∑ i ∈ s, f j i ^ p j
      rw [← Real.rpow_mul (hNnonneg j hj), inv_mul_cancel₀ (hp j hj).ne', Real.rpow_one]
    have hprodCpos : 0 < ∏ j ∈ t, C j := prod_pos fun j hj => hCpos j hj
    rw [← div_le_one hprodCpos]
    have hrw : (∑ i ∈ s, ∏ j ∈ t, f j i) / (∏ j ∈ t, C j)
        = ∑ i ∈ s, ∏ j ∈ t, f j i / C j := by
      rw [sum_div]
      exact sum_congr rfl fun i hi => (prod_div_distrib _ _).symm
    rw [hrw]
    calc
      ∑ i ∈ s, ∏ j ∈ t, f j i / C j
          ≤ ∑ i ∈ s, ∑ j ∈ t, (p j)⁻¹ * (f j i / C j) ^ p j := by
            refine sum_le_sum fun i hi => ?_
            exact young_product t (fun j => f j i / C j) p
              (fun j hj => div_nonneg (hf j hj i hi) (hCpos j hj).le) hp hsum
      _ = ∑ j ∈ t, (p j)⁻¹ * ∑ i ∈ s, (f j i / C j) ^ p j := by
            rw [sum_comm]
            exact sum_congr rfl fun j hj => (mul_sum _ _ _).symm
      _ = ∑ j ∈ t, (p j)⁻¹ * 1 := by
            refine sum_congr rfl fun j hj => ?_
            congr 1
            have hpoint : ∑ i ∈ s, (f j i / C j) ^ p j
                = ∑ i ∈ s, f j i ^ p j / C j ^ p j :=
              sum_congr rfl fun i hi => Real.div_rpow (hf j hj i hi) (hCpos j hj).le _
            rw [hpoint, ← sum_div, hCp j hj, div_self (hNpos j hj).ne']
      _ = 1 := by simp only [mul_one]; exact hsum

/-- **Two-function (classical) Hölder inequality** for finite sums, as the `t = {0, 1}`
specialization of `generalized_holder`.  For nonnegative `u v : ι → ℝ` and conjugate exponents
`1 < p`, `1 < q` with `p⁻¹ + q⁻¹ = 1`,
`∑ i, u i * v i ≤ (∑ i, u i ^ p) ^ p⁻¹ * (∑ i, v i ^ q) ^ q⁻¹`. -/
theorem inner_le_holder_two (s : Finset ι) (u v : ι → ℝ) (p q : ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (hp : 0 < p) (hq : 0 < q) (hpq : p⁻¹ + q⁻¹ = 1) :
    ∑ i ∈ s, u i * v i
      ≤ (∑ i ∈ s, u i ^ p) ^ p⁻¹ * (∑ i ∈ s, v i ^ q) ^ q⁻¹ := by
  have h := generalized_holder s (univ : Finset (Fin 2))
    (fun j i => if j = 0 then u i else v i) (fun j => if j = 0 then p else q)
    (by intro j _ i hi; fin_cases j <;> simp [hu i hi, hv i hi])
    (by intro j _; fin_cases j <;> simp [hp, hq])
    (by simp [Fin.sum_univ_two, hpq])
  simpa [Fin.sum_univ_two, Fin.prod_univ_two] using h

end JensenHolder
