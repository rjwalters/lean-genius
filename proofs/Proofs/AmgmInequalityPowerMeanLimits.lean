/-
  Power Mean Extreme Cases: Limits as r → ±∞

  ## Open Question: amgm-inequality-oq-03-oq-03-incomplete-01

  Proves:
    lim_{r → +∞} M_r(x₁,...,xₙ) = max(xᵢ)
    lim_{r → -∞} M_r(x₁,...,xₙ) = min(xᵢ)

  The proof strategy:
  - For r → +∞: squeeze  max · n^(-1/r) ≤ M_r ≤ max  with n^(-1/r) → 1
  - For r → -∞: use duality  M_{-r}(x) = 1/M_r(1/x)  and the +∞ result

  Parent: AmgmInequalityOQ03OQ03.lean
-/

import Mathlib

namespace AmgmPowerMeanLimits

open Filter Real Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable (x : ι → ℝ)

/-- The unweighted power mean M_r = ((∑ xᵢʳ) / n)^(1/r). -/
noncomputable def M (r : ℝ) : ℝ :=
  ((∑ i : ι, x i ^ r) / Fintype.card ι) ^ (1 / r)

private lemma hN_pos : (0 : ℝ) < (Fintype.card ι : ℝ) :=
  Nat.cast_pos.mpr Fintype.card_pos

private lemma hN_ne : (Fintype.card ι : ℝ) ≠ 0 :=
  (hN_pos).ne'

-- ============================================================
-- Section 1: Key helper — c^(1/r) → 1 as r → +∞
-- ============================================================

/-- For c > 0, c^(r⁻¹) → 1 as r → +∞. -/
private theorem tendsto_rpow_inv_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℝ => c ^ r⁻¹) atTop (nhds 1) := by
  have hinner : Tendsto (fun r : ℝ => log c * r⁻¹) atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.const_mul (log c)
    simp only [mul_zero] at h; exact h
  have hexp : Tendsto Real.exp (nhds 0) (nhds (Real.exp 0)) := continuous_exp.continuousAt
  have hcomp := hexp.comp hinner
  simp only [Real.exp_zero] at hcomp
  exact hcomp.congr (fun r => (rpow_def_of_pos hc r⁻¹).symm)

-- ============================================================
-- Section 2: Anti-monotone rpow for negative exponents
-- ============================================================

/-- For 0 < a ≤ b: b⁻¹ ≤ a⁻¹. -/
private lemma aux_inv_le_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  calc b⁻¹
      = b⁻¹ * (a * a⁻¹) := by rw [mul_inv_cancel₀ ha.ne', mul_one]
    _ ≤ b⁻¹ * (b * a⁻¹) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hab (inv_pos.mpr ha).le)
            (inv_pos.mpr hb).le
    _ = a⁻¹ := by rw [← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul]

/-- For 0 < a ≤ b and z ≤ 0: b^z ≤ a^z. -/
private lemma rpow_le_rpow_of_nonpos {a b z : ℝ} (ha : 0 < a) (hab : a ≤ b) (hz : z ≤ 0) :
    b ^ z ≤ a ^ z := by
  rcases hz.eq_or_lt with rfl | hz
  · simp
  · have hn : 0 ≤ -z := neg_nonneg.mpr hz.le
    rw [show z = -(-z) from (neg_neg z).symm,
        rpow_neg ha.le, rpow_neg (le_trans ha.le hab)]
    exact aux_inv_le_inv (rpow_pos_of_pos ha _) (rpow_le_rpow ha.le hab hn)

-- ============================================================
-- Section 3: Max value
-- ============================================================

/-- Maximum of x over the finite type. -/
noncomputable def maxX : ℝ := Finset.univ.sup' Finset.univ_nonempty x

lemma le_maxX (i : ι) : x i ≤ maxX x :=
  Finset.le_sup' x (Finset.mem_univ i)

lemma maxX_pos (hx : ∀ i, 0 < x i) : 0 < maxX x :=
  lt_of_lt_of_le (hx Finset.univ_nonempty.choose)
    (le_maxX x Finset.univ_nonempty.choose)

private lemma exists_maxX (hx : ∀ i, 0 < x i) : ∃ i₀ : ι, x i₀ = maxX x := by
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  exact ⟨i₀, le_antisymm (le_maxX x i₀)
    (Finset.sup'_le Finset.univ_nonempty x (fun i _ => hi₀ i (Finset.mem_univ i)))⟩

-- ============================================================
-- Section 4: Max bound theorems
-- ============================================================

/-- For r > 0: M_r ≤ max(xᵢ). -/
theorem M_le_maxX (hx : ∀ i, 0 < x i) (hr : 0 < r) :
    M x r ≤ maxX x := by
  simp only [M]
  have hMx : 0 ≤ maxX x := le_of_lt (maxX_pos x hx)
  have hbnd : ∀ i : ι, x i ^ r ≤ (maxX x) ^ r := fun i =>
    rpow_le_rpow (le_of_lt (hx i)) (le_maxX x i) hr.le
  have hsdiv : (∑ i : ι, x i ^ r) / Fintype.card ι ≤ (maxX x) ^ r := by
    have key : ∑ i : ι, x i ^ r ≤ (maxX x) ^ r * Fintype.card ι :=
      calc ∑ i : ι, x i ^ r
          ≤ ∑ _i : ι, (maxX x) ^ r := sum_le_sum (fun i _ => hbnd i)
        _ = Fintype.card ι * (maxX x) ^ r := by simp [sum_const, card_univ, nsmul_eq_mul]
        _ = (maxX x) ^ r * Fintype.card ι := mul_comm _ _
    calc (∑ i : ι, x i ^ r) / Fintype.card ι
        ≤ ((maxX x) ^ r * Fintype.card ι) / Fintype.card ι :=
            div_le_div_of_nonneg_right key hN_pos.le
      _ = (maxX x) ^ r := mul_div_cancel_right₀ _ hN_ne
  calc ((∑ i : ι, x i ^ r) / Fintype.card ι) ^ (1 / r)
      ≤ ((maxX x) ^ r) ^ (1 / r) :=
        rpow_le_rpow
          (div_nonneg (sum_nonneg (fun i _ => rpow_nonneg (le_of_lt (hx i)) _)) (hN_pos).le)
          hsdiv (div_nonneg zero_le_one hr.le)
    _ = maxX x := by
        rw [← rpow_mul hMx, mul_one_div_cancel (ne_of_gt hr)]
        exact rpow_one _

/-- For r > 0: max(xᵢ) · n^(-1/r) ≤ M_r. -/
theorem maxX_mul_rpow_le_M (hx : ∀ i, 0 < x i) (hr : 0 < r) :
    maxX x * (Fintype.card ι : ℝ) ^ (-(1 / r)) ≤ M x r := by
  simp only [M]
  obtain ⟨i₀, hi₀⟩ := exists_maxX x hx
  have hMx : 0 < maxX x := maxX_pos x hx
  have hslb : (maxX x) ^ r ≤ ∑ i : ι, x i ^ r := by
    calc (maxX x) ^ r = x i₀ ^ r := by rw [hi₀]
      _ ≤ ∑ i : ι, x i ^ r :=
          single_le_sum (fun i _ => rpow_nonneg (le_of_lt (hx i)) _) (mem_univ i₀)
  have hdiv_lb : (maxX x) ^ r / Fintype.card ι ≤ (∑ i : ι, x i ^ r) / Fintype.card ι :=
    div_le_div_of_nonneg_right hslb (hN_pos).le
  have h1r : (0 : ℝ) < 1 / r := div_pos one_pos hr
  -- (maxX^r / n)^(1/r) = maxX · n^(-1/r)
  have hrhs : ((maxX x) ^ r / (Fintype.card ι : ℝ)) ^ (1 / r) =
      maxX x * (Fintype.card ι : ℝ) ^ (-(1 / r)) := by
    rw [div_rpow (rpow_nonneg hMx.le _) (hN_pos).le]
    rw [← rpow_mul hMx.le, one_div, mul_inv_cancel₀ (ne_of_gt hr), rpow_one]
    rw [rpow_neg (hN_pos).le, div_eq_mul_inv]
  rw [← hrhs]
  exact rpow_le_rpow (div_nonneg (rpow_nonneg hMx.le _) (hN_pos).le)
    hdiv_lb h1r.le

-- ============================================================
-- Section 5: Limit as r → +∞
-- ============================================================

/-- M_r → max(xᵢ) as r → +∞. -/
theorem tendsto_M_atTop (hx : ∀ i, 0 < x i) :
    Tendsto (M x) atTop (nhds (maxX x)) := by
  -- Lower bound: maxX · n^(-1/r) → maxX
  have hlb : Tendsto (fun r : ℝ => maxX x * (Fintype.card ι : ℝ) ^ (-(1 / r))) atTop
      (nhds (maxX x)) := by
    have hn_tend : Tendsto (fun r : ℝ => (Fintype.card ι : ℝ) ^ (-(1 / r))) atTop (nhds 1) := by
      -- (card ι)^(-(1/r)) = ((card ι)^(1/r))⁻¹ → 1⁻¹ = 1
      have h : Tendsto (fun r : ℝ => ((Fintype.card ι : ℝ) ^ r⁻¹)⁻¹) atTop (nhds 1) := by
        have key : Tendsto (fun r : ℝ => (Fintype.card ι : ℝ) ^ r⁻¹) atTop (nhds 1) :=
          tendsto_rpow_inv_atTop hN_pos
        have := key.inv₀ (one_pos (α := ℝ)).ne'
        simp only [inv_one] at this; exact this
      refine h.congr' ?_
      filter_upwards with r
      rw [one_div, rpow_neg hN_pos.le]
    have hmul := hn_tend.const_mul (maxX x)
    simp only [mul_one] at hmul
    exact hmul.congr' (by filter_upwards with r; ring)
  -- Squeeze
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlb tendsto_const_nhds
    ((eventually_gt_atTop 0).mono (fun r hr => maxX_mul_rpow_le_M x hx hr))
    ((eventually_gt_atTop 0).mono (fun r hr => M_le_maxX x hx hr))

-- ============================================================
-- Section 6: Duality  M_{-r}(x) = 1 / M_r(1/x)
-- ============================================================

/-- M_{-r}(x) = (M_r(1/x))⁻¹ for positive xᵢ and r ≠ 0. -/
lemma M_neg_eq_inv_M_inv (hx : ∀ i, 0 < x i) {r : ℝ} (hr : r ≠ 0) :
    M x (-r) = (M (fun i => (x i)⁻¹) r)⁻¹ := by
  simp only [M]
  have hsum_nn : 0 ≤ (∑ i : ι, x i ^ (-r)) / Fintype.card ι :=
    div_nonneg (sum_nonneg (fun i _ => rpow_nonneg (le_of_lt (hx i)) _)) (hN_pos).le
  have heq : (∑ i : ι, x i ^ (-r)) = (∑ i : ι, (x i)⁻¹ ^ r) := by
    apply Finset.sum_congr rfl; intro i _
    rw [inv_rpow (le_of_lt (hx i)), rpow_neg (le_of_lt (hx i))]
  rw [show (1 : ℝ) / (-r) = -(1 / r) by ring, rpow_neg hsum_nn, heq]

-- ============================================================
-- Section 7: Min value and min = 1/max(1/x)
-- ============================================================

/-- Minimum of x over the finite type. -/
noncomputable def minX : ℝ := Finset.univ.inf' Finset.univ_nonempty x

lemma minX_le (i : ι) : minX x ≤ x i :=
  Finset.inf'_le x (Finset.mem_univ i)

private lemma exists_minX (hx : ∀ i, 0 < x i) : ∃ i₀ : ι, x i₀ = minX x := by
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  exact ⟨i₀, le_antisymm
    (Finset.le_inf' Finset.univ_nonempty x (fun j _ => hi₀ j (Finset.mem_univ j)))
    (Finset.inf'_le x (Finset.mem_univ i₀))⟩

lemma minX_pos (hx : ∀ i, 0 < x i) : 0 < minX x := by
  obtain ⟨i₀, hi₀⟩ := exists_minX x hx; exact hi₀ ▸ hx i₀

/-- min(x) = (max(1/x))⁻¹ for positive xᵢ. -/
lemma minX_eq_inv_maxX_inv (hx : ∀ i, 0 < x i) :
    minX x = (maxX (fun i => (x i)⁻¹))⁻¹ := by
  have hm : 0 < minX x := minX_pos x hx
  have hM : 0 < maxX (fun i => (x i)⁻¹) := maxX_pos _ (fun i => inv_pos.mpr (hx i))
  apply le_antisymm
  · -- minX x ≤ (maxX y)⁻¹: show maxX y ≤ (minX x)⁻¹, i.e. each (x i)⁻¹ ≤ (minX x)⁻¹
    rw [← inv_inv (minX x)]
    apply aux_inv_le_inv hM
    apply Finset.sup'_le Finset.univ_nonempty
    intro i _
    exact aux_inv_le_inv hm (minX_le x i)
  · -- (maxX y)⁻¹ ≤ x i₀ = minX x
    obtain ⟨i₀, hi₀⟩ := exists_minX x hx
    calc (maxX (fun i => (x i)⁻¹))⁻¹
        ≤ ((x i₀)⁻¹)⁻¹ :=
            aux_inv_le_inv (inv_pos.mpr (hx i₀)) (le_maxX (fun i => (x i)⁻¹) i₀)
      _ = x i₀ := inv_inv _
      _ = minX x := hi₀

-- ============================================================
-- Section 8: Limit as r → -∞ (via duality)
-- ============================================================

/-- M_r → min(xᵢ) as r → -∞. -/
theorem tendsto_M_atBot (hx : ∀ i, 0 < x i) :
    Tendsto (M x) atBot (nhds (minX x)) := by
  let y := fun i => (x i)⁻¹
  have hy : ∀ i, 0 < y i := fun i => inv_pos.mpr (hx i)
  -- M y r → maxX y as r → +∞
  have hmax : Tendsto (M y) atTop (nhds (maxX y)) := tendsto_M_atTop y hy
  -- (M y r)⁻¹ → (maxX y)⁻¹ = minX x
  have hMaxNe : maxX y ≠ 0 := (maxX_pos y hy).ne'
  have hminmax : (maxX y)⁻¹ = minX x := (minX_eq_inv_maxX_inv x hx).symm
  have hinv : Tendsto (fun r => (M y r)⁻¹) atTop (nhds (minX x)) := by
    rw [← hminmax]; exact hmax.inv₀ hMaxNe
  -- M x (-s) = (M y s)⁻¹ for s ≠ 0
  have hdual : ∀ s : ℝ, s ≠ 0 → M x (-s) = (M y s)⁻¹ :=
    fun s hs => M_neg_eq_inv_M_inv x hx hs
  -- Tendsto (fun s => M x (-s)) atTop (nhds (minX x))
  have hcomp : Tendsto (fun s : ℝ => M x (-s)) atTop (nhds (minX x)) :=
    hinv.congr' ((eventually_ne_atTop (0 : ℝ)).mono (fun s hs => (hdual s hs).symm))
  -- Conclude Tendsto (M x) atBot (nhds (minX x))
  -- Compose hcomp with negation: Neg.neg sends atBot to atTop
  exact (hcomp.comp tendsto_neg_atBot_atTop).congr (fun r => congr_arg (M x) (neg_neg r))

-- ============================================================
-- Summary theorems
-- ============================================================

/-- The power mean converges to the maximum as the exponent → +∞. -/
theorem powerMean_tendsto_max (hx : ∀ i, 0 < x i) :
    Tendsto (fun r : ℝ => ((∑ i : ι, x i ^ r) / Fintype.card ι) ^ (1 / r))
      atTop (nhds (Finset.univ.sup' Finset.univ_nonempty x)) :=
  tendsto_M_atTop x hx

/-- The power mean converges to the minimum as the exponent → -∞. -/
theorem powerMean_tendsto_min (hx : ∀ i, 0 < x i) :
    Tendsto (fun r : ℝ => ((∑ i : ι, x i ^ r) / Fintype.card ι) ^ (1 / r))
      atBot (nhds (Finset.univ.inf' Finset.univ_nonempty x)) :=
  tendsto_M_atBot x hx

end AmgmPowerMeanLimits
