/-
  AM-GM OQ-03-OQ-02-OQ-04: Extreme Power Mean Limits

  The power mean M_r(x) = (Σ xᵢ^r / n)^{1/r} at the extremes:
    lim_{r → +∞} M_r(x) = max(x₁,...,xₙ)
    lim_{r → -∞} M_r(x) = min(x₁,...,xₙ)

  Proof strategy (squeeze theorem):
    For r > 0: max * n^{-1/r} ≤ M_r ≤ max
    Since max * n^{-1/r} → max * 1 = max, we have M_r → max.
    The min case follows by applying the max case to {1/xᵢ}.

  Parent: amgm-inequality-oq-03-oq-02 (lim_{r→0} M_r = GM)
-/
import Mathlib

namespace AmgmOQ03OQ02OQ04

open Real Filter Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

-- ═══════════════════════════════════════════════════════════════
-- PART I: POWER MEAN DEFINITION
-- ═══════════════════════════════════════════════════════════════

/-- Unweighted power mean at exponent r. -/
noncomputable def powerMean (x : ι → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then (∏ i : ι, x i) ^ ((Fintype.card ι : ℝ)⁻¹)
  else ((∑ i : ι, (x i) ^ r) / Fintype.card ι) ^ (1 / r)

-- ═══════════════════════════════════════════════════════════════
-- PART II: KEY LIMIT: c^(-1/r) → 1 AS r → +∞
-- ═══════════════════════════════════════════════════════════════

/-- For any c > 0, c^(-1/r) → 1 as r → +∞. -/
lemma tendsto_const_rpow_neg_inv_atTop {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun r : ℝ => c ^ (-r⁻¹)) Filter.atTop (nhds 1) := by
  -- Step 1: -r⁻¹ → 0 as r → +∞
  have h_inv : Filter.Tendsto (fun r : ℝ => r⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have h_neg : Filter.Tendsto (fun r : ℝ => -r⁻¹) Filter.atTop (nhds 0) := by
    simpa [neg_zero] using h_inv.neg
  -- Step 2: c^t → c^0 = 1 as t → 0 (by continuity of c^·)
  -- Use Tendsto.rpow: Tendsto c (atTop) (nhds c) and Tendsto (-r⁻¹) (atTop) (nhds 0)
  have h_rpow : Filter.Tendsto (fun r : ℝ => c ^ (-r⁻¹)) Filter.atTop (nhds (c ^ (0 : ℝ))) := by
    exact tendsto_const_nhds.rpow h_neg (Or.inl (ne_of_gt hc))
  simp [Real.rpow_zero] at h_rpow
  exact h_rpow

-- ═══════════════════════════════════════════════════════════════
-- PART III: BOUNDS ON POWER MEAN
-- ═══════════════════════════════════════════════════════════════

private lemma card_pos : 0 < (Fintype.card ι : ℝ) :=
  Nat.cast_pos.mpr Fintype.card_pos

/-- For r > 0, powerMean x r ≤ sup'(x). -/
lemma powerMean_le_sup (x : ι → ℝ) (hx : ∀ i, 0 < x i) {r : ℝ} (hr : 0 < r) :
    powerMean x r ≤ Finset.univ.sup' Finset.univ_nonempty x := by
  simp only [powerMean, if_neg (ne_of_gt hr)]
  set M := Finset.univ.sup' Finset.univ_nonempty x
  have hM : 0 < M := lt_of_lt_of_le (hx (Classical.arbitrary ι))
    (Finset.le_sup' x (Finset.mem_univ _))
  -- Each xᵢ ≤ M, so xᵢ^r ≤ M^r (for r > 0)
  have hle : ∀ i, (x i) ^ r ≤ M ^ r := fun i =>
    Real.rpow_le_rpow (le_of_lt (hx i)) (Finset.le_sup' x (Finset.mem_univ i)) (le_of_lt hr)
  -- Sum xᵢ^r ≤ n * M^r
  have hsum : ∑ i : ι, (x i) ^ r ≤ Fintype.card ι * M ^ r := by
    calc ∑ i : ι, (x i) ^ r ≤ ∑ _ : ι, M ^ r :=
          Finset.sum_le_sum (fun i _ => hle i)
      _ = Fintype.card ι * M ^ r := by
          simp [Finset.sum_const, Finset.card_univ]
  -- (sum/n)^{1/r} ≤ (M^r)^{1/r} = M
  have hn := card_pos (ι := ι)
  have hdiv : (∑ i : ι, (x i) ^ r) / (Fintype.card ι : ℝ) ≤ M ^ r := by
    have h : (Fintype.card ι : ℝ) * ((∑ i : ι, (x i) ^ r) / (Fintype.card ι : ℝ)) ≤
             (Fintype.card ι : ℝ) * M ^ r := by
      rw [mul_div_cancel₀ _ (ne_of_gt hn)]; linarith
    exact le_of_mul_le_mul_left h hn
  calc ((∑ i : ι, (x i) ^ r) / Fintype.card ι) ^ (1 / r)
      ≤ (M ^ r) ^ (1 / r) :=
        Real.rpow_le_rpow
          (div_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (le_of_lt (hx i)) r)
            (le_of_lt hn))
          hdiv (le_of_lt (by positivity))
    _ = M := by
        rw [one_div, ← Real.rpow_mul (le_of_lt hM)]
        simp [mul_inv_cancel₀ (ne_of_gt hr)]

/-- For r > 0, sup'(x) * n^(-1/r) ≤ powerMean x r. -/
lemma sup_mul_pow_le_powerMean (x : ι → ℝ) (hx : ∀ i, 0 < x i) {r : ℝ} (hr : 0 < r) :
    Finset.univ.sup' Finset.univ_nonempty x * (Fintype.card ι : ℝ) ^ (-r⁻¹) ≤
    powerMean x r := by
  simp only [powerMean, if_neg (ne_of_gt hr)]
  set M := Finset.univ.sup' Finset.univ_nonempty x
  have hM : 0 < M := lt_of_lt_of_le (hx (Classical.arbitrary ι))
    (Finset.le_sup' x (Finset.mem_univ _))
  have hn := card_pos (ι := ι)
  -- There exists i₀ achieving the maximum
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image Finset.univ x
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have hmax : M = x i₀ := le_antisymm
    (Finset.sup'_le _ _ (fun j _ => hi₀ j (Finset.mem_univ j)))
    (Finset.le_sup' x (Finset.mem_univ i₀))
  -- Sum xᵢ^r ≥ M^r (contribution from i₀)
  have hsum : M ^ r ≤ ∑ i : ι, (x i) ^ r := by
    calc M ^ r = (x i₀) ^ r := by rw [hmax]
      _ ≤ ∑ i : ι, (x i) ^ r := Finset.single_le_sum
          (fun i _ => le_of_lt (Real.rpow_pos_of_pos (hx i) r))
          (Finset.mem_univ i₀)
  -- Rewrite M * n^{-1/r} = (M^r / n)^{1/r}
  have hrhs : M * (Fintype.card ι : ℝ) ^ (-r⁻¹) =
      (M ^ r / Fintype.card ι) ^ r⁻¹ := by
    rw [Real.div_rpow (Real.rpow_nonneg (le_of_lt hM) r) (le_of_lt hn),
        ← Real.rpow_mul (le_of_lt hM), mul_inv_cancel₀ (ne_of_gt hr), Real.rpow_one,
        Real.rpow_neg (le_of_lt hn), div_eq_mul_inv]
  calc M * (Fintype.card ι : ℝ) ^ (-r⁻¹)
      = (M ^ r / Fintype.card ι) ^ r⁻¹ := hrhs
    _ ≤ ((∑ i : ι, (x i) ^ r) / Fintype.card ι) ^ (1 / r) := by
        rw [one_div]
        have hle : M ^ r / (Fintype.card ι : ℝ) ≤ (∑ i : ι, (x i) ^ r) / (Fintype.card ι : ℝ) := by
          apply le_of_mul_le_mul_left _ hn
          rw [mul_div_cancel₀ _ (ne_of_gt hn), mul_div_cancel₀ _ (ne_of_gt hn)]
          exact hsum
        exact Real.rpow_le_rpow (by positivity) hle (by positivity)

-- ═══════════════════════════════════════════════════════════════
-- PART IV: MAIN THEOREM
-- ═══════════════════════════════════════════════════════════════

/-- Main theorem: powerMean x r → max(x) as r → +∞. -/
theorem powerMean_tendsto_max (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    Filter.Tendsto (fun r => powerMean x r) Filter.atTop
      (nhds (Finset.univ.sup' Finset.univ_nonempty x)) := by
  set M := Finset.univ.sup' Finset.univ_nonempty x
  have hn := card_pos (ι := ι)
  -- Lower bound: M * n^{-1/r} → M
  have h_lower : Filter.Tendsto (fun r : ℝ => M * (Fintype.card ι : ℝ) ^ (-r⁻¹))
      Filter.atTop (nhds M) := by
    have h1 := tendsto_const_rpow_neg_inv_atTop hn
    simpa [mul_one] using tendsto_const_nhds (x := M).mul h1
  -- Upper bound: M (constant) → M
  have h_upper : Filter.Tendsto (fun _ : ℝ => M) Filter.atTop (nhds M) :=
    tendsto_const_nhds
  -- Squeeze
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower h_upper
  · filter_upwards [eventually_gt_atTop 0] with r hr
    exact sup_mul_pow_le_powerMean x hx hr
  · filter_upwards [eventually_gt_atTop 0] with r hr
    exact powerMean_le_sup x hx hr

/-- Corollary: powerMean x r → min(x) as r → -∞.
    Proved by applying the max case to the inverse function. -/
theorem powerMean_tendsto_min (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    Filter.Tendsto (fun r => powerMean x r) Filter.atBot
      (nhds (Finset.univ.inf' Finset.univ_nonempty x)) := by
  -- Strategy: apply the max case to g = 1/x, then use the identity
  -- powerMean x r = (powerMean g (-r))⁻¹ for r ≠ 0
  set g := fun i => (x i)⁻¹ with hg_def
  have hg : ∀ i, 0 < g i := fun i => inv_pos.mpr (hx i)
  -- Find i₀ achieving the minimum of x
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_min_image Finset.univ x
    ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  set m := Finset.univ.inf' Finset.univ_nonempty x
  have hm_eq : m = x i₀ := le_antisymm
    (Finset.inf'_le x (Finset.mem_univ i₀))
    (Finset.le_inf' Finset.univ_nonempty x (fun j _ => hi₀ j (Finset.mem_univ j)))
  have hm_pos : 0 < m := by rw [hm_eq]; exact hx i₀
  -- sup'(g) = m⁻¹: taking inverses reverses the order
  have h_sup_g : Finset.univ.sup' Finset.univ_nonempty g = m⁻¹ := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      simp only [hg_def]
      -- (x i)⁻¹ ≤ m⁻¹ because m ≤ x i (inline proof of antitone inv)
      have hxi := hx i
      have hle : m ≤ x i := Finset.inf'_le x (Finset.mem_univ i)
      calc (x i)⁻¹
          = (x i)⁻¹ * (m * m⁻¹) := by rw [mul_inv_cancel₀ hm_pos.ne', mul_one]
        _ ≤ (x i)⁻¹ * (x i * m⁻¹) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hle (inv_pos.mpr hm_pos).le)
                (inv_pos.mpr hxi).le
        _ = m⁻¹ := by rw [← mul_assoc, inv_mul_cancel₀ hxi.ne', one_mul]
    · calc m⁻¹ = g i₀ := by simp [hg_def, hm_eq]
        _ ≤ Finset.univ.sup' Finset.univ_nonempty g :=
            Finset.le_sup' g (Finset.mem_univ i₀)
  -- Apply max theorem to g: powerMean g r → sup'(g) = m⁻¹ as r → +∞
  have h_max : Filter.Tendsto (fun r => powerMean g r) Filter.atTop (nhds m⁻¹) := by
    have := powerMean_tendsto_max g hg
    rwa [h_sup_g] at this
  -- Invert: (powerMean g r)⁻¹ → m as r → +∞
  have h_inv : Filter.Tendsto (fun r => (powerMean g r)⁻¹) Filter.atTop (nhds m) := by
    have h := h_max.inv₀ (inv_ne_zero hm_pos.ne')
    rwa [inv_inv] at h
  -- Algebraic identity: for r < 0, (powerMean g (-r))⁻¹ = powerMean x r
  -- Uses: (xᵢ⁻¹)^(-r) = xᵢ^r  via  inv_rpow + rpow_neg + inv_inv
  have h_ident : ∀ᶠ r in Filter.atBot, (powerMean g (-r))⁻¹ = powerMean x r := by
    filter_upwards [Filter.eventually_lt_atBot 0] with r hr
    have hrne : r ≠ 0 := ne_of_lt hr
    have hnrne : -r ≠ 0 := neg_ne_zero.mpr hrne
    simp only [powerMean, if_neg hrne, if_neg hnrne, hg_def]
    -- Σ (x i)⁻¹ ^ (-r) = Σ (x i) ^ r
    have hsum : ∑ i : ι, ((x i)⁻¹) ^ (-r) = ∑ i : ι, (x i) ^ r := by
      congr 1; ext i
      rw [Real.inv_rpow (le_of_lt (hx i)), Real.rpow_neg (le_of_lt (hx i)), inv_inv]
    rw [hsum]
    -- ((S/n)^(1/(-r)))⁻¹ = (S/n)^(1/r)
    have hS_nonneg : 0 ≤ (∑ i : ι, (x i) ^ r) / Fintype.card ι :=
      div_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (le_of_lt (hx i)) r)
        (le_of_lt card_pos)
    rw [← Real.rpow_neg hS_nonneg (1 / (-r))]
    congr 1
    rw [div_neg, neg_neg]
  -- Compose: atBot →(negation)→ atTop, then apply h_inv, then congr with identity
  exact (h_inv.comp Filter.tendsto_neg_atBot_atTop).congr' h_ident

end AmgmOQ03OQ02OQ04
