import Mathlib
import Proofs.CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ03OQ02

/-
# Strict Monotonicity of the Weighted Power Mean Chain: WHM < WGM < WAM < WQM ⇔ a ≠ b

## Research Problem: cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-03-oq-02-oq-02

Two ancestors set the stage for the two-point weighted means of positive reals
`a, b` with positive weights `w₁, w₂` summing to `1`:

  - `…OQ02OQ03.lean`     (`WeightedPowerMeanChain`)   proved the *non-strict* chain
    `WHM ≤ WGM ≤ WAM ≤ WQM`;
  - `…OQ02OQ03OQ02.lean` (`WeightedPowerMeanEquality`) proved the *equality case*:
    each individual link is an equality **iff** `a = b`
    (`whm_eq_wgm_iff`, `wgm_eq_wam_iff`, `wam_eq_wqm_iff`), so the whole chain
    collapses to one value iff `a = b`.

The remaining open question is the **strict** form: off the diagonal `a ≠ b`, is each
inequality *strict*?

## Answer: YES — and it is "all or nothing"

Combining a non-strict link (`≤`) with its equality characterization (`= ⇔ a = b`)
upgrades it to a strict link exactly when `a ≠ b`. We record each link as an `iff`:

  - `whm_lt_wgm_iff_ne` : `WHM < WGM ⇔ a ≠ b`
  - `wgm_lt_wam_iff_ne` : `WGM < WAM ⇔ a ≠ b`
  - `wam_lt_wqm_iff_ne` : `WAM < WQM ⇔ a ≠ b`

so all three links are controlled by the *same* scalar condition `a ≠ b`. Hence the
headline rigidity dichotomy

  - `strict_chain_iff_ne`      : `(WHM < WGM ∧ WGM < WAM ∧ WAM < WQM) ⇔ a ≠ b`,
  - `any_strict_iff_all_strict`: a *single* strict gap forces *all* gaps strict.

The chain has no "intermediate" regime: either `a = b` and every mean coincides, or
`a ≠ b` and every inequality is strict simultaneously. We close with the classical
equal-weight specialization `unweighted_strict_chain_of_ne`:
`2ab/(a+b) < √(ab) < (a+b)/2 < √((a²+b²)/2)` for `a ≠ b`.

### Technique

We import the parent (equality case), reusing its three `= ⇔ a = b` links and the
ready-made strict gap `wam_lt_wqm_of_ne`. The two remaining non-strict links
`WHM ≤ WGM` and `WGM ≤ WAM` are re-derived here as short private lemmas
(`whm_le_wgm_aux`, `wgm_le_wam_aux`) directly from Mathlib's two-variable weighted
AM–GM, so the file depends only on the parent and Mathlib. Each strict link is then
`LE.le.lt_of_ne`: the `≤` together with the `≠` supplied by the contrapositive of the
parent's `= ⇔ a = b`. No new analytic input is required — the strictness is a pure
consequence of the equality characterization, which is what makes the dichotomy clean.

Tags: inequalities, power-means, weighted, AM-GM, strict, monotonicity, rigidity, research
-/

namespace WeightedPowerMeanStrict

open Real WeightedPowerMeanEquality

variable {a b w₁ w₂ : ℝ}

-- ============================================================
-- Part 0: The two non-strict links we still need (≤), inlined
--          from Mathlib's two-variable weighted AM–GM.
-- ============================================================

/-- `(1/a)^w₁ · (1/b)^w₂ = (a^w₁ · b^w₂)⁻¹` for `a, b > 0`. -/
private lemma inv_wgm_eq (ha : 0 < a) (hb : 0 < b) :
    (1 / a) ^ w₁ * (1 / b) ^ w₂ = (a ^ w₁ * b ^ w₂)⁻¹ := by
  have ha' := Real.rpow_pos_of_pos ha w₁
  have hb' := Real.rpow_pos_of_pos hb w₂
  rw [Real.div_rpow (by norm_num) ha.le, Real.div_rpow (by norm_num) hb.le,
      Real.one_rpow, Real.one_rpow]
  field_simp [ne_of_gt ha', ne_of_gt hb']

/-- `WGM ≤ WAM` — the two-variable weighted AM–GM (Mathlib). -/
private lemma wgm_le_wam_aux (ha : 0 ≤ a) (hb : 0 ≤ b) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hw : w₁ + w₂ = 1) : WGM w₁ w₂ a b ≤ WAM w₁ w₂ a b := by
  unfold WGM WAM
  exact Real.geom_mean_le_arith_mean2_weighted hw₁ hw₂ ha hb hw

/-- `WHM ≤ WGM` — apply weighted AM–GM to the reciprocals and invert.
    Strict weights `0 < w₁, w₂` make the harmonic denominator strictly positive. -/
private lemma whm_le_wgm_aux (ha : 0 < a) (hb : 0 < b) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hw : w₁ + w₂ = 1) : WHM w₁ w₂ a b ≤ WGM w₁ w₂ a b := by
  unfold WHM WGM
  have hWGM_pos : 0 < a ^ w₁ * b ^ w₂ := by positivity
  have hWHM_inv_pos : 0 < w₁ / a + w₂ / b := by positivity
  have h_amgm := Real.geom_mean_le_arith_mean2_weighted hw₁.le hw₂.le
    (by positivity : (0 : ℝ) ≤ 1 / a) (by positivity : (0 : ℝ) ≤ 1 / b) hw
  rw [inv_wgm_eq ha hb] at h_amgm
  have hrhs : w₁ * (1 / a) + w₂ * (1 / b) = w₁ / a + w₂ / b := by ring
  rw [hrhs] at h_amgm
  rwa [inv_le_comm₀ hWHM_inv_pos hWGM_pos]

-- ============================================================
-- Part I: The three strict links (≤ upgraded by a ≠ b)
-- ============================================================

/-- **Strict Harmonic–Geometric link.** `WHM < WGM` when `a ≠ b`.
    The `≤` is `whm_le_wgm_aux`; equality is excluded by `whm_eq_wgm_iff`. -/
theorem whm_lt_wgm_of_ne (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) (hab : a ≠ b) :
    WHM w₁ w₂ a b < WGM w₁ w₂ a b :=
  (whm_le_wgm_aux ha hb hw₁ hw₂ hw).lt_of_ne
    (fun h => hab ((whm_eq_wgm_iff ha hb hw₁ hw₂ hw).mp h))

/-- **Strict Geometric–Arithmetic link.** `WGM < WAM` when `a ≠ b` (strict AM–GM).
    The `≤` is `wgm_le_wam_aux`; equality is excluded by `wgm_eq_wam_iff`. -/
theorem wgm_lt_wam_of_ne (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) (hab : a ≠ b) :
    WGM w₁ w₂ a b < WAM w₁ w₂ a b :=
  (wgm_le_wam_aux ha.le hb.le hw₁.le hw₂.le hw).lt_of_ne
    (fun h => hab ((wgm_eq_wam_iff ha hb hw₁ hw₂ hw).mp h))

/-- **Strict Arithmetic–Quadratic link.** `WAM < WQM` when `a ≠ b`.
    Re-exported from `WeightedPowerMeanEquality.wam_lt_wqm_of_ne` (the "positive
    variance" gap) for symmetry with the other two links. -/
theorem wam_lt_wqm_of_ne (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) (hab : a ≠ b) :
    WAM w₁ w₂ a b < WQM w₁ w₂ a b :=
  WeightedPowerMeanEquality.wam_lt_wqm_of_ne ha hb hw₁ hw₂ hw hab

-- ============================================================
-- Part II: Each link is governed by the single condition a ≠ b
-- ============================================================

/-- `WHM < WGM ⇔ a ≠ b`. -/
theorem whm_lt_wgm_iff_ne (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) :
    WHM w₁ w₂ a b < WGM w₁ w₂ a b ↔ a ≠ b :=
  ⟨fun h => (whm_eq_wgm_iff ha hb hw₁ hw₂ hw).not.mp h.ne,
   whm_lt_wgm_of_ne ha hb hw₁ hw₂ hw⟩

/-- `WGM < WAM ⇔ a ≠ b`. -/
theorem wgm_lt_wam_iff_ne (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) :
    WGM w₁ w₂ a b < WAM w₁ w₂ a b ↔ a ≠ b :=
  ⟨fun h => (wgm_eq_wam_iff ha hb hw₁ hw₂ hw).not.mp h.ne,
   wgm_lt_wam_of_ne ha hb hw₁ hw₂ hw⟩

/-- `WAM < WQM ⇔ a ≠ b`. -/
theorem wam_lt_wqm_iff_ne (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) :
    WAM w₁ w₂ a b < WQM w₁ w₂ a b ↔ a ≠ b :=
  ⟨fun h => (wam_eq_wqm_iff ha hb hw₁ hw₂ hw).not.mp h.ne,
   wam_lt_wqm_of_ne ha hb hw₁ hw₂ hw⟩

-- ============================================================
-- Part III: Headline — the strict chain and its rigidity
-- ============================================================

/-- **Strict weighted power mean chain.** For `a ≠ b`, every link is strict:
    `WHM < WGM < WAM < WQM`. -/
theorem strict_chain_of_ne (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) (hab : a ≠ b) :
    WHM w₁ w₂ a b < WGM w₁ w₂ a b ∧
    WGM w₁ w₂ a b < WAM w₁ w₂ a b ∧
    WAM w₁ w₂ a b < WQM w₁ w₂ a b :=
  ⟨whm_lt_wgm_of_ne ha hb hw₁ hw₂ hw hab,
   wgm_lt_wam_of_ne ha hb hw₁ hw₂ hw hab,
   wam_lt_wqm_of_ne ha hb hw₁ hw₂ hw hab⟩

/-- **Strictness ⇔ off-diagonal.** The full strict chain holds iff `a ≠ b`. -/
theorem strict_chain_iff_ne (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) :
    (WHM w₁ w₂ a b < WGM w₁ w₂ a b ∧
     WGM w₁ w₂ a b < WAM w₁ w₂ a b ∧
     WAM w₁ w₂ a b < WQM w₁ w₂ a b) ↔ a ≠ b :=
  ⟨fun ⟨h, _, _⟩ => (whm_lt_wgm_iff_ne ha hb hw₁ hw₂ hw).mp h,
   strict_chain_of_ne ha hb hw₁ hw₂ hw⟩

/-- **Rigidity dichotomy ("all or nothing").** A *single* strict gap anywhere in the
    chain forces *every* gap to be strict. Equivalently: the means are either all
    equal (`a = b`) or pairwise strictly ordered (`a ≠ b`); there is no intermediate
    regime where some links are tight and others slack. -/
theorem any_strict_iff_all_strict (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) :
    (WHM w₁ w₂ a b < WGM w₁ w₂ a b ∨
     WGM w₁ w₂ a b < WAM w₁ w₂ a b ∨
     WAM w₁ w₂ a b < WQM w₁ w₂ a b) ↔
    (WHM w₁ w₂ a b < WGM w₁ w₂ a b ∧
     WGM w₁ w₂ a b < WAM w₁ w₂ a b ∧
     WAM w₁ w₂ a b < WQM w₁ w₂ a b) := by
  constructor
  · intro h
    have hab : a ≠ b := by
      rcases h with h | h | h
      · exact (whm_lt_wgm_iff_ne ha hb hw₁ hw₂ hw).mp h
      · exact (wgm_lt_wam_iff_ne ha hb hw₁ hw₂ hw).mp h
      · exact (wam_lt_wqm_iff_ne ha hb hw₁ hw₂ hw).mp h
    exact strict_chain_of_ne ha hb hw₁ hw₂ hw hab
  · rintro ⟨h, _, _⟩; exact Or.inl h

-- ============================================================
-- Part IV: Equal-weight specialization (classical statement)
-- ============================================================

/-- **Classical strict chain** at `w₁ = w₂ = 1/2`: for `a ≠ b`,
    `2ab/(a+b) < √(ab) < (a+b)/2 < √((a²+b²)/2)`
    (HM < GM < AM < QM in explicit textbook form). -/
theorem unweighted_strict_chain_of_ne (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    2 * a * b / (a + b) < Real.sqrt (a * b) ∧
    Real.sqrt (a * b) < (a + b) / 2 ∧
    (a + b) / 2 < Real.sqrt ((a ^ 2 + b ^ 2) / 2) := by
  -- Identify each mean at equal weights with its textbook form.
  have hHM : WHM (1/2) (1/2) a b = 2 * a * b / (a + b) := by
    unfold WHM
    have ha' : a ≠ 0 := ha.ne'
    have hb' : b ≠ 0 := hb.ne'
    have hab' : a + b ≠ 0 := by linarith
    field_simp; ring
  have hGM : WGM (1/2) (1/2) a b = Real.sqrt (a * b) := by
    unfold WGM
    rw [← Real.mul_rpow ha.le hb.le, ← Real.sqrt_eq_rpow]
  have hAM : WAM (1/2) (1/2) a b = (a + b) / 2 := by unfold WAM; ring
  have hQM : WQM (1/2) (1/2) a b = Real.sqrt ((a ^ 2 + b ^ 2) / 2) := by
    unfold WQM; congr 1; ring
  obtain ⟨h1, h2, h3⟩ := strict_chain_of_ne (a := a) (b := b) (w₁ := 1/2) (w₂ := 1/2)
    ha hb (by norm_num) (by norm_num) (by norm_num) hab
  rw [hHM, hGM] at h1
  rw [hGM, hAM] at h2
  rw [hAM, hQM] at h3
  exact ⟨h1, h2, h3⟩

end WeightedPowerMeanStrict
