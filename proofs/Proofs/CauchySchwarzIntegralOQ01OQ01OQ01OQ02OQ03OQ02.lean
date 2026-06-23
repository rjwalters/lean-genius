import Mathlib

/-
# Equality Case of the Weighted Power Mean Chain: WHM = WGM = WAM = WQM ⇔ a = b

## Research Problem: cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-03-oq-02

The parent file `CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ03.lean` proved the weighted
power mean chain WHM ≤ WGM ≤ WAM ≤ WQM for two positive reals `a, b` and weights
`w₁, w₂ > 0` with `w₁ + w₂ = 1`. Its open question #2 asks:

> Does the equality case WHM = WGM = WAM = WQM ⇔ a = b extend to the weighted setting?

## Answer: YES

We prove that the entire chain collapses to a single value **iff** `a = b`, and we
isolate the equality condition for *each individual link*:

  - `wam_eq_wqm_iff` : WAM = WQM ⇔ a = b   (quadratic vs arithmetic; "zero variance")
  - `wgm_eq_wam_iff` : WGM = WAM ⇔ a = b   (geometric vs arithmetic; AM–GM equality)
  - `whm_eq_wgm_iff` : WHM = WGM ⇔ a = b   (harmonic vs geometric; reciprocal duality)

and the headline collapse

  - `chain_eq_iff`   : (WHM = WGM ∧ WGM = WAM ∧ WAM = WQM) ⇔ a = b.

We also record the strict form `wam_lt_wqm_of_ne` (the quadratic-arithmetic gap is
*strict* when `a ≠ b`) and the equal-weight specialization recovering the classical
statement HM = GM = AM = QM ⇔ a = b.

### Techniques

- **WAM = WQM**: the weighted-variance identity
  `w₁·a² + w₂·b² − (w₁·a + w₂·b)² = w₁·w₂·(a − b)²`. With `w₁, w₂ > 0` the right side
  vanishes iff `a = b`. This is the cleanest "pinch" — it alone forces `a = b`, so the
  whole chain collapse needs nothing deeper than `ring` + `Real.sqrt`.
- **WGM = WAM**: Mathlib's AM–GM equality condition
  `Real.geom_mean_eq_arith_mean_weighted_iff'` instantiated at the two-point space
  `Fin 2` with weights `![w₁, w₂]` and values `![a, b]`.
- **WHM = WGM**: reciprocal duality `WHM(a,b)⁻¹ = WAM(1/a,1/b)`,
  `WGM(a,b)⁻¹ = WGM(1/a,1/b)`, reducing to the WGM = WAM case applied to `(1/a, 1/b)`.

Tags: inequalities, power-means, weighted, AM-GM, equality-case, Jensen, research
-/

namespace WeightedPowerMeanEquality

open Real

variable {a b w₁ w₂ : ℝ}

-- ============================================================
-- Part I: Definitions (mirroring the parent file)
-- ============================================================

/-- Weighted harmonic mean: (w₁/a + w₂/b)⁻¹ -/
noncomputable def WHM (w₁ w₂ a b : ℝ) : ℝ := (w₁ / a + w₂ / b)⁻¹

/-- Weighted geometric mean: a^w₁ · b^w₂ -/
noncomputable def WGM (w₁ w₂ a b : ℝ) : ℝ := a ^ w₁ * b ^ w₂

/-- Weighted arithmetic mean: w₁·a + w₂·b -/
noncomputable def WAM (w₁ w₂ a b : ℝ) : ℝ := w₁ * a + w₂ * b

/-- Weighted quadratic mean: √(w₁·a² + w₂·b²) -/
noncomputable def WQM (w₁ w₂ a b : ℝ) : ℝ := Real.sqrt (w₁ * a ^ 2 + w₂ * b ^ 2)

-- ============================================================
-- Part II: The collapse value when a = b
-- ============================================================

/-- When `a = b`, the weighted harmonic mean equals `a`. -/
theorem whm_eq_of_eq (ha : 0 < a) (hw : w₁ + w₂ = 1) :
    WHM w₁ w₂ a a = a := by
  unfold WHM
  rw [← add_div, hw]
  rw [one_div, inv_inv]

/-- When `a = b`, the weighted geometric mean equals `a`. -/
theorem wgm_eq_of_eq (ha : 0 < a) (hw : w₁ + w₂ = 1) :
    WGM w₁ w₂ a a = a := by
  unfold WGM
  rw [← Real.rpow_add ha, hw, Real.rpow_one]

/-- When `a = b`, the weighted arithmetic mean equals `a`. -/
theorem wam_eq_of_eq (hw : w₁ + w₂ = 1) :
    WAM w₁ w₂ a a = a := by
  unfold WAM
  rw [← add_mul, hw, one_mul]

/-- When `a = b`, the weighted quadratic mean equals `a`. -/
theorem wqm_eq_of_eq (ha : 0 ≤ a) (hw : w₁ + w₂ = 1) :
    WQM w₁ w₂ a a = a := by
  unfold WQM
  rw [← add_mul, hw, one_mul, Real.sqrt_sq ha]

-- ============================================================
-- Part III: The weighted-variance identity
-- ============================================================

/-- **Weighted variance identity.** For weights summing to 1,
    `w₁·a² + w₂·b² − (w₁·a + w₂·b)² = w₁·w₂·(a − b)²`. -/
theorem weighted_variance_eq (hw : w₁ + w₂ = 1) :
    w₁ * a ^ 2 + w₂ * b ^ 2 - (w₁ * a + w₂ * b) ^ 2 = w₁ * w₂ * (a - b) ^ 2 := by
  have h : w₂ = 1 - w₁ := by linarith
  rw [h]; ring

-- ============================================================
-- Part IV: WAM = WQM ⇔ a = b   (the "zero variance" link)
-- ============================================================

/-- **Quadratic–Arithmetic equality.** `WAM = WQM ⇔ a = b`. -/
theorem wam_eq_wqm_iff (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) :
    WAM w₁ w₂ a b = WQM w₁ w₂ a b ↔ a = b := by
  constructor
  · intro h
    -- WAM ≥ 0 and WAM = WQM ⟹ WAM² = WQM² = w₁a² + w₂b²
    have hsq : (w₁ * a + w₂ * b) ^ 2 = w₁ * a ^ 2 + w₂ * b ^ 2 := by
      have hsq' : WAM w₁ w₂ a b ^ 2 = WQM w₁ w₂ a b ^ 2 := by rw [h]
      unfold WAM WQM at hsq'
      rwa [Real.sq_sqrt (by positivity)] at hsq'
    -- variance identity forces w₁·w₂·(a-b)² = 0
    have hvar : w₁ * w₂ * (a - b) ^ 2 = 0 := by
      have := weighted_variance_eq (a := a) (b := b) hw
      linarith
    have hne : w₁ * w₂ ≠ 0 := by positivity
    have hzero : (a - b) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hvar with h' | h'
      · exact absurd h' hne
      · exact h'
    have : a - b = 0 := by nlinarith [sq_nonneg (a - b)]
    linarith
  · intro h; subst h
    rw [wam_eq_of_eq hw, wqm_eq_of_eq ha.le hw]

/-- **Strict Quadratic–Arithmetic inequality** when `a ≠ b`: `WAM < WQM`. -/
theorem wam_lt_wqm_of_ne (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) (hab : a ≠ b) :
    WAM w₁ w₂ a b < WQM w₁ w₂ a b := by
  -- WAM ≤ WQM (from squares) and WAM ≠ WQM (equality forces a = b)
  have hwam_nn : 0 ≤ w₁ * a + w₂ * b := by positivity
  have hle : WAM w₁ w₂ a b ≤ WQM w₁ w₂ a b := by
    unfold WAM WQM
    rw [← Real.sqrt_sq hwam_nn]
    apply Real.sqrt_le_sqrt
    have hvar := weighted_variance_eq (a := a) (b := b) hw
    nlinarith [mul_pos hw₁ hw₂, sq_nonneg (a - b)]
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd ((wam_eq_wqm_iff ha hb hw₁ hw₂ hw).mp h) hab

-- ============================================================
-- Part V: WGM = WAM ⇔ a = b   (AM–GM equality, via Mathlib)
-- ============================================================

/-- Two-point repackaging: over `Fin 2` with weights `![w₁, w₂]` and values `![a, b]`,
    the geometric and arithmetic means are exactly `WGM` and `WAM`. -/
private lemma fin2_prod (a b w₁ w₂ : ℝ) :
    ∏ i : Fin 2, (![a, b] i) ^ (![w₁, w₂] i) = a ^ w₁ * b ^ w₂ := by
  simp [Fin.prod_univ_two]

private lemma fin2_sum (a b w₁ w₂ : ℝ) :
    ∑ i : Fin 2, (![w₁, w₂] i) * (![a, b] i) = w₁ * a + w₂ * b := by
  simp [Fin.sum_univ_two]

/-- **Geometric–Arithmetic equality.** `WGM = WAM ⇔ a = b`. -/
theorem wgm_eq_wam_iff (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) :
    WGM w₁ w₂ a b = WAM w₁ w₂ a b ↔ a = b := by
  have hwsum : ∑ i : Fin 2, (![w₁, w₂] i) = 1 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; linarith
  have hwpos : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 < (![w₁, w₂] i) := by
    intro i _; fin_cases i
    · simpa using hw₁
    · simpa using hw₂
  have hznn : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ (![a, b] i) := by
    intro i _; fin_cases i
    · simpa using ha.le
    · simpa using hb.le
  have key := Real.geom_mean_eq_arith_mean_weighted_iff'
    (Finset.univ : Finset (Fin 2)) ![w₁, w₂] ![a, b] hwpos hwsum hznn
  rw [fin2_prod, fin2_sum] at key
  -- key : a^w₁ * b^w₂ = w₁*a + w₂*b ↔ ∀ j, ![a,b] j = w₁*a + w₂*b
  unfold WGM WAM
  rw [key]
  constructor
  · intro h
    have h0 := h 0 (Finset.mem_univ _)
    have h1 := h 1 (Finset.mem_univ _)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    -- h0 : a = w₁*a + w₂*b, h1 : b = w₁*a + w₂*b
    linarith
  · intro h j _
    subst h
    have hsum : w₁ * a + w₂ * a = a := by rw [← add_mul, hw, one_mul]
    rw [hsum]
    fin_cases j <;> rfl

-- ============================================================
-- Part VI: WHM = WGM ⇔ a = b   (reciprocal duality)
-- ============================================================

/-- Reciprocal of the harmonic mean is the arithmetic mean of the reciprocals. -/
private lemma inv_whm (ha : 0 < a) (hb : 0 < b) :
    (WHM w₁ w₂ a b)⁻¹ = WAM w₁ w₂ (1 / a) (1 / b) := by
  unfold WHM WAM
  rw [inv_inv]
  ring

/-- Reciprocal of the geometric mean is the geometric mean of the reciprocals. -/
private lemma inv_wgm (ha : 0 < a) (hb : 0 < b) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) :
    (WGM w₁ w₂ a b)⁻¹ = WGM w₁ w₂ (1 / a) (1 / b) := by
  unfold WGM
  rw [Real.div_rpow (by norm_num) ha.le, Real.div_rpow (by norm_num) hb.le,
      Real.one_rpow, Real.one_rpow, mul_inv]
  rw [one_div, one_div]

/-- **Harmonic–Geometric equality.** `WHM = WGM ⇔ a = b`. -/
theorem whm_eq_wgm_iff (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) :
    WHM w₁ w₂ a b = WGM w₁ w₂ a b ↔ a = b := by
  have hWHM : 0 < WHM w₁ w₂ a b := by
    unfold WHM; apply inv_pos.mpr; positivity
  have hWGM : 0 < WGM w₁ w₂ a b := by unfold WGM; positivity
  -- WHM = WGM ⇔ WHM⁻¹ = WGM⁻¹ ⇔ WAM(1/a,1/b) = WGM(1/a,1/b) ⇔ 1/a = 1/b ⇔ a = b
  rw [show (WHM w₁ w₂ a b = WGM w₁ w₂ a b) ↔
        ((WHM w₁ w₂ a b)⁻¹ = (WGM w₁ w₂ a b)⁻¹) from
        ⟨fun h => by rw [h], fun h => by
          have h' := congrArg (·⁻¹) h
          simpa using h'⟩]
  rw [inv_whm ha hb, inv_wgm ha hb hw₁.le hw₂.le, eq_comm]
  rw [wgm_eq_wam_iff (by positivity) (by positivity) hw₁ hw₂ hw]
  constructor
  · intro h
    have h' : (1 / a)⁻¹ = (1 / b)⁻¹ := by rw [h]
    simpa [one_div] using h'
  · intro h; rw [h]

-- ============================================================
-- Part VII: Headline — the whole chain collapses iff a = b
-- ============================================================

/-- **Equality case of the weighted power mean chain.**
    `WHM = WGM = WAM = WQM ⇔ a = b`.

    The forward direction needs only the `WAM = WQM` link (zero variance);
    the backward direction shows every mean collapses to the common value `a`. -/
theorem chain_eq_iff (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) :
    (WHM w₁ w₂ a b = WGM w₁ w₂ a b ∧
     WGM w₁ w₂ a b = WAM w₁ w₂ a b ∧
     WAM w₁ w₂ a b = WQM w₁ w₂ a b) ↔ a = b := by
  constructor
  · rintro ⟨_, _, h3⟩
    exact (wam_eq_wqm_iff ha hb hw₁ hw₂ hw).mp h3
  · intro h; subst h
    refine ⟨?_, ?_, ?_⟩
    · rw [whm_eq_of_eq ha hw, wgm_eq_of_eq ha hw]
    · rw [wgm_eq_of_eq ha hw, wam_eq_of_eq hw]
    · rw [wam_eq_of_eq hw, wqm_eq_of_eq ha.le hw]

/-- Equivalent packaging: all four means coincide with the arithmetic mean iff `a = b`. -/
theorem all_means_eq_iff (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) :
    (WHM w₁ w₂ a b = WAM w₁ w₂ a b ∧
     WGM w₁ w₂ a b = WAM w₁ w₂ a b ∧
     WQM w₁ w₂ a b = WAM w₁ w₂ a b) ↔ a = b := by
  constructor
  · rintro ⟨_, _, h3⟩
    exact (wam_eq_wqm_iff ha hb hw₁ hw₂ hw).mp h3.symm
  · intro h; subst h
    refine ⟨?_, ?_, ?_⟩
    · rw [whm_eq_of_eq ha hw, wam_eq_of_eq hw]
    · rw [wgm_eq_of_eq ha hw, wam_eq_of_eq hw]
    · rw [wqm_eq_of_eq ha.le hw, wam_eq_of_eq hw]

-- ============================================================
-- Part VIII: Equal-weight specialization (classical statement)
-- ============================================================

/-- **Classical equality case** at `w₁ = w₂ = 1/2`:
    `HM = GM = AM = QM ⇔ a = b`, in the explicit textbook forms. -/
theorem unweighted_chain_eq_iff (ha : 0 < a) (hb : 0 < b) :
    (2 * a * b / (a + b) = Real.sqrt (a * b) ∧
     Real.sqrt (a * b) = (a + b) / 2 ∧
     (a + b) / 2 = Real.sqrt ((a ^ 2 + b ^ 2) / 2)) ↔ a = b := by
  have hHM : WHM (1/2) (1/2) a b = 2 * a * b / (a + b) := by
    unfold WHM
    have ha' : a ≠ 0 := ha.ne'
    have hb' : b ≠ 0 := hb.ne'
    have hab' : a + b ≠ 0 := by linarith
    field_simp
    ring
  have hGM : WGM (1/2) (1/2) a b = Real.sqrt (a * b) := by
    unfold WGM
    rw [← Real.mul_rpow ha.le hb.le, ← Real.sqrt_eq_rpow]
  have hAM : WAM (1/2) (1/2) a b = (a + b) / 2 := by unfold WAM; ring
  have hQM : WQM (1/2) (1/2) a b = Real.sqrt ((a ^ 2 + b ^ 2) / 2) := by
    unfold WQM; congr 1; ring
  have base := chain_eq_iff (a := a) (b := b) (w₁ := 1/2) (w₂ := 1/2)
    ha hb (by norm_num) (by norm_num) (by norm_num)
  rw [hHM, hGM, hAM, hQM] at base
  exact base

end WeightedPowerMeanEquality
