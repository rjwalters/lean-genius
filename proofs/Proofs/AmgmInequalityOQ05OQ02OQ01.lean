/-
  The classical (unweighted) AM-GM inequality and its equality case, over `Fin n`.

  The parent entry `amgm-inequality-oq-05-oq-02` established the **weighted**
  AM-GM *equality case* for an arbitrary finite index set: for strictly positive
  weights `w` summing to `1` and strictly positive `x`,

      ∏ i, (x i) ^ (w i)  =  ∑ i, w i * x i    ↔    all the `xⱼ` are equal.

  Its first stated open question was to specialise this to **equal weights**
  `wᵢ = 1/n` and read off the classical statement that everyone knows as
  "AM-GM": the geometric mean of `n` positive reals is at most their arithmetic
  mean, with equality iff the numbers are all equal.  That is exactly what this
  file does, in the canonical form indexed over `Fin n`:

      geometric mean  G = (∏ i, x i) ^ (1/n),      arithmetic mean  A = (∑ i, x i) / n,

      G ≤ A            (`classical_amgm_le`),
      G = A  ↔  all `xᵢ` equal   (`classical_amgm_eq_iff`).

  The inequality direction is a direct specialisation of Mathlib's
  `Real.geom_mean_le_arith_mean` (weights `≡ 1`).  The equality characterisation
  is *not* in Mathlib; we obtain it from the strict concavity of `Real.log`
  (`strictConcaveOn_log_Ioi`) via the equality case of Jensen's inequality
  `StrictConcaveOn.map_sum_eq_iff`, exactly as the parent did, then convert the
  weighted geometric mean `∏ (x i) ^ (1/n)` into `(∏ x i) ^ (1/n)` with
  `Real.finset_prod_rpow`.

  All exponents are real, so `^` denotes `Real.rpow` throughout.

  Verified: 0 sorries, 0 axioms.
-/
import Mathlib

open Real Finset

namespace AmgmInequalityOQ05OQ02OQ01

variable {ι : Type*}

/-! ### Reusable engine: the weighted equality case (self-contained)

These three helpers plus `weighted_amgm_eq_iff_pairwise` reproduce, in
self-contained form, the weighted AM-GM equality case that the parent entry
proved.  We keep them `private`: the point of this entry is the *classical*
`Fin n` specialisation below, for which they are merely scaffolding. -/

/-- Taking logs turns the weighted geometric mean into the weighted sum of
logarithms: `log (∏ xᵢ ^ wᵢ) = ∑ wᵢ · log xᵢ`. -/
private theorem log_prod_rpow {t : Finset ι} {w x : ι → ℝ} (hx : ∀ i ∈ t, 0 < x i) :
    Real.log (∏ i ∈ t, x i ^ w i) = ∑ i ∈ t, w i * Real.log (x i) := by
  rw [Real.log_prod (fun i hi => (Real.rpow_pos_of_pos (hx i hi) (w i)).ne')]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Real.log_rpow (hx i hi)]

/-- The weighted geometric mean of positive reals is positive. -/
private theorem prod_rpow_pos {t : Finset ι} {w x : ι → ℝ} (hx : ∀ i ∈ t, 0 < x i) :
    0 < ∏ i ∈ t, x i ^ w i :=
  Finset.prod_pos (fun i hi => Real.rpow_pos_of_pos (hx i hi) (w i))

/-- The weighted arithmetic mean of positive reals with positive weights, over a
nonempty index set, is positive. -/
private theorem mean_pos {t : Finset ι} {w x : ι → ℝ} (hw : ∀ i ∈ t, 0 < w i)
    (hx : ∀ i ∈ t, 0 < x i) (hne : t.Nonempty) :
    0 < ∑ i ∈ t, w i * x i :=
  Finset.sum_pos (fun i hi => mul_pos (hw i hi) (hx i hi)) hne

/-- **Weighted AM-GM equality case (pairwise form).**  Equality between the
weighted geometric and arithmetic means holds iff all the `xⱼ` are equal. -/
private theorem weighted_amgm_eq_iff_pairwise {t : Finset ι} {w x : ι → ℝ}
    (hw : ∀ i ∈ t, 0 < w i) (hsum : ∑ i ∈ t, w i = 1) (hx : ∀ i ∈ t, 0 < x i) :
    (∏ i ∈ t, x i ^ w i = ∑ i ∈ t, w i * x i) ↔
      (∀ i ∈ t, ∀ j ∈ t, x i = x j) := by
  have hne : t.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hsum
  have hA : 0 < ∑ i ∈ t, w i * x i := mean_pos hw hx hne
  have hP : 0 < ∏ i ∈ t, x i ^ w i := prod_rpow_pos hx
  -- Equality of the two positive means is equality of their logs.
  rw [← Real.log_injOn_pos.eq_iff (Set.mem_Ioi.mpr hP) (Set.mem_Ioi.mpr hA),
      log_prod_rpow hx, eq_comm]
  -- The strict concavity of `log` supplies the equality case of Jensen.
  have key := strictConcaveOn_log_Ioi.map_sum_eq_iff (t := t) (w := w) (p := x)
      hw hsum (fun i hi => Set.mem_Ioi.mpr (hx i hi))
  simp only [smul_eq_mul] at key
  rw [key]
  -- `∀ j, x j = mean` is equivalent to `∀ i j, x i = x j`.
  constructor
  · intro h i hi j hj; rw [h i hi, h j hj]
  · intro h j hj
    have hconst : ∑ i ∈ t, w i * x i = ∑ i ∈ t, w i * x j := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [h i hi j hj]
    rw [hconst, ← Finset.sum_mul, hsum, one_mul]

/-! ### The classical `Fin n` statement -/

variable {n : ℕ}

/-- The `n` equal weights `1/n` sum to `1` over `Fin n`. -/
private theorem sum_inv_card (hn : 0 < n) :
    ∑ _i : Fin n, (n : ℝ)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_inv_cancel₀ (by exact_mod_cast hn.ne')]

/-- **Classical AM-GM inequality** for `n` nonnegative reals: the geometric mean
`(∏ xᵢ)^{1/n}` is at most the arithmetic mean `(∑ xᵢ)/n`.

This is `Real.geom_mean_le_arith_mean` specialised to the uniform weights `1`. -/
theorem classical_amgm_le (hn : 0 < n) {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    (∏ i, x i) ^ (n : ℝ)⁻¹ ≤ (∑ i, x i) / n := by
  have hcard : ∑ _i : Fin n, (1 : ℝ) = (n : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have key := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin n))
      (fun _ => (1 : ℝ)) x (fun _ _ => zero_le_one)
      (by rw [hcard]; exact_mod_cast hn) (fun i _ => hx i)
  simpa only [Real.rpow_one, one_mul, hcard] using key

/-- **Classical AM-GM equality case** for `n` strictly positive reals: the
geometric mean `(∏ xᵢ)^{1/n}` equals the arithmetic mean `(∑ xᵢ)/n` **iff all
the `xᵢ` are equal**.

This is the unweighted specialisation (weights `1/n`) of the parent entry's
weighted equality case, repackaged into the canonical geometric-mean form via
`Real.finset_prod_rpow`. -/
theorem classical_amgm_eq_iff (hn : 0 < n) {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) :
    (∏ i, x i) ^ (n : ℝ)⁻¹ = (∑ i, x i) / n ↔ ∀ i j, x i = x j := by
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 < (n : ℝ)⁻¹ :=
    fun _ _ => by positivity
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin n)), (n : ℝ)⁻¹ = 1 := sum_inv_card hn
  have hxpos : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 < x i := fun i _ => hx i
  have base := weighted_amgm_eq_iff_pairwise (w := fun _ => (n : ℝ)⁻¹) (x := x)
      hw hsum hxpos
  -- Convert `∏ (x i)^{1/n}` into `(∏ x i)^{1/n}`.
  have hprod : ∏ i ∈ (Finset.univ : Finset (Fin n)), x i ^ (n : ℝ)⁻¹
      = (∏ i, x i) ^ (n : ℝ)⁻¹ :=
    Real.finset_prod_rpow Finset.univ x (fun i _ => (hx i).le) _
  -- Convert `∑ (1/n) * x i` into `(∑ x i)/n`.
  have hmean : ∑ i ∈ (Finset.univ : Finset (Fin n)), (n : ℝ)⁻¹ * x i
      = (∑ i, x i) / n := by
    rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]
  rw [hprod, hmean] at base
  simpa using base

/-- The trivial direction, recorded explicitly: if all `xᵢ` are equal then the
geometric and arithmetic means coincide. -/
theorem classical_amgm_eq_of_const (hn : 0 < n) {x : Fin n → ℝ} {c : ℝ}
    (hx : ∀ i, 0 < x i) (hc : ∀ i, x i = c) :
    (∏ i, x i) ^ (n : ℝ)⁻¹ = (∑ i, x i) / n :=
  (classical_amgm_eq_iff hn hx).mpr (fun i j => (hc i).trans (hc j).symm)

/-- **Strict classical AM-GM**: if the `xᵢ` are not all equal, the geometric mean
is *strictly* below the arithmetic mean. -/
theorem classical_amgm_lt_of_not_const (hn : 0 < n) {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) (hne : ∃ i j, x i ≠ x j) :
    (∏ i, x i) ^ (n : ℝ)⁻¹ < (∑ i, x i) / n := by
  refine lt_of_le_of_ne (classical_amgm_le hn (fun i => (hx i).le)) ?_
  intro hEq
  obtain ⟨i, j, hij⟩ := hne
  exact hij ((classical_amgm_eq_iff hn hx).mp hEq i j)

end AmgmInequalityOQ05OQ02OQ01
