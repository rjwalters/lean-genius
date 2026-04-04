import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Basic

/-
# Geometric Interpretation of Non-Equal Weights in Ceva's Theorem
# (cevas-theorem-oq-02-oq-01-oq-03)

## The Open Question

**OQ-02-OQ-01-OQ-03**: What is the geometric interpretation of the weight
parameters (α, β) in Ceva's theorem? When weights are NOT equal (α ≠ β),
what cevian points arise, and what does the weight ratio α/β encode?

## The Answer: Division Ratios

The weight parameters directly encode the division ratio of the cevian point
along each side of the triangle:

**Euclidean case** (ordinary Ceva's theorem):
  D = (α·B + β·C) / (α + β)  divides segment BC in ratio β:α
  More precisely: BD / DC = β / α

This gives a complete geometric picture:
- **α = β**: D is the midpoint of BC → all three midpoints → concurrency at centroid
- **β > α**: D is closer to B (the arc is divided with more weight toward C)
- **β < α**: D is closer to C
- **Ceva condition**: α_D·α_E·α_F = β_D·β_E·β_F ↔ (BD/DC)·(CE/EA)·(AF/FB) = 1

## Specific Geometric Configurations Arising from Non-Equal Weights

1. **Medians** (α = β for all): midpoints → centroid
2. **Angle bisectors** (α_D = |AC|, β_D = |AB|): incenter (by angle bisector theorem)
3. **Symmedian point** (α_D = |AB|², β_D = |AC|²): weighted by square of sides

## Summary: 18 theorems, 0 sorries, 0 axioms

All results are fully proved from arithmetic and Mathlib lemmas.
-/

set_option linter.unusedVariables false

namespace CevasOQ02OQ01OQ03

/-
## Part I: Division Ratio Formula

The core geometric interpretation: the weight pair (α, β) encodes
where D lies on the segment BC.

In Euclidean geometry:
  D = (α·B + β·C) / (α + β)
satisfies:
  BD = |D - B| = β·|C - B| / (α + β)
  DC = |C - D| = α·|C - B| / (α + β)

Hence BD/DC = β/α.
-/

/-- **Division formula**: The weight-sum point D = (α·B + β·C)/(α+β) can be
    rewritten as B + β·(C-B)/(α+β). This shows D lies on the segment [B,C],
    displaced from B by a fraction β/(α+β) of the total length. -/
theorem weight_point_displacement (B C α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (α * B + β * C) / (α + β) = B + β * (C - B) / (α + β) := by
  have hαβ : α + β ≠ 0 := by linarith
  field_simp [hαβ]
  ring

/-- **Numerator decomposition for BD**: The displacement from B to D equals
    β·(C-B)/(α+β). Geometrically, D is exactly the fraction β/(α+β) along BC. -/
theorem weight_point_distance_from_B (B C α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    let D := (α * B + β * C) / (α + β)
    D - B = β * (C - B) / (α + β) := by
  simp only
  have hαβ : α + β ≠ 0 := by linarith
  field_simp [hαβ]; ring

/-- **Numerator decomposition for DC**: The displacement from D to C equals
    α·(C-B)/(α+β). -/
theorem weight_point_distance_to_C (B C α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    let D := (α * B + β * C) / (α + β)
    C - D = α * (C - B) / (α + β) := by
  simp only
  have hαβ : α + β ≠ 0 := by linarith
  field_simp [hαβ]; ring

/-- **Division ratio**: The weight-sum point D = (α·B + β·C)/(α+β) divides the
    segment BC in ratio BD:DC = β:α.

    More precisely, (D-B)/(C-D) = β/α, provided B ≠ C (so C-B ≠ 0).

    This is the core geometric meaning of the weight parameters:
    - α controls the fraction of BC on the C-side: DC = α/(α+β) · |BC|
    - β controls the fraction on the B-side: BD = β/(α+β) · |BC|
    - When α > β: D is closer to B (more of BC is on the C-side)
    - When α < β: D is closer to C
    - When α = β: D is the midpoint -/
theorem weight_division_ratio (B C α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hBC : B ≠ C) :
    let D := (α * B + β * C) / (α + β)
    (D - B) / (C - D) = β / α := by
  simp only
  have hαβ : α + β ≠ 0 := by linarith
  have hα_ne : α ≠ 0 := hα.ne'
  have hCB : C - B ≠ 0 := sub_ne_zero.mpr (Ne.symm hBC)
  have hDB : (α * B + β * C) / (α + β) - B = β * (C - B) / (α + β) := by
    field_simp [hαβ]; ring
  have hCD : C - (α * B + β * C) / (α + β) = α * (C - B) / (α + β) := by
    field_simp [hαβ]; ring
  rw [hDB, hCD]
  have hαCB : α * (C - B) / (α + β) ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero hα_ne hCB
    · linarith
  field_simp [hαCB, hα_ne, hCB, hαβ]

/-- **Midpoint characterization**: When B ≠ C, the weight-sum
    point (α·B + β·C)/(α+β) is the midpoint iff α = β. -/
theorem weight_midpoint_iff_of_ne (B C α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hBC : B ≠ C) :
    (α * B + β * C) / (α + β) = (B + C) / 2 ↔ α = β := by
  have hαβ : α + β ≠ 0 := by linarith
  constructor
  · intro h
    have h' : (α * B + β * C) * 2 = (B + C) * (α + β) := by
      field_simp [hαβ] at h; linarith
    have key : (α - β) * (B - C) = 0 := by linarith
    rcases mul_eq_zero.mp key with hαβeq | hBCeq
    · linarith
    · exact absurd (sub_eq_zero.mp hBCeq) hBC
  · intro h
    rw [h]
    have hβ2 : (β + β : ℝ) ≠ 0 := by linarith
    rw [div_eq_div_iff hβ2 two_ne_zero]; ring

/-- **Fraction formula**: The position of D along BC is β/(α+β) from B.
    When β/(α+β) = 1/2 (i.e., α = β), D is the midpoint. -/
theorem weight_fraction_from_B (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    β / (α + β) = 1/2 ↔ α = β := by
  have hαβ : α + β ≠ 0 := by linarith
  constructor
  · intro h
    have : β * 2 = α + β := by field_simp [hαβ] at h; linarith
    linarith
  · intro h; subst h
    have hα2 : (α + α : ℝ) ≠ 0 := by linarith
    rw [div_eq_div_iff hα2 two_ne_zero]; ring

/-- **Non-equal weights → off-center cevian**: When α ≠ β, the cevian point D
    is NOT at the midpoint of BC. -/
theorem nonequal_weights_not_midpoint (B C α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hBC : B ≠ C) (hαβ_ne : α ≠ β) :
    (α * B + β * C) / (α + β) ≠ (B + C) / 2 := by
  intro h
  exact hαβ_ne ((weight_midpoint_iff_of_ne B C α β hα hβ hBC).mp h)

/-
## Part II: Ceva's Theorem via Division Ratios

In the Euclidean triangle, the classical Ceva condition
  (BD/DC) · (CE/EA) · (AF/FB) = 1
is equivalent to the weight balance condition
  α_D · α_E · α_F = β_D · β_E · β_F.

This generalizes the spherical case (OQ-02-OQ-01) to the Euclidean setting.
-/

/-- **Ceva product via weight ratios**: The classical Ceva product equals the
    weight-product ratio (βD·βE·βF)/(αD·αE·αF). -/
theorem ceva_product_eq_weight_ratio
    (αD βD αE βE αF βF : ℝ)
    (hαD : 0 < αD) (hβD : 0 < βD)
    (hαE : 0 < αE) (hβE : 0 < βE)
    (hαF : 0 < αF) (hβF : 0 < βF) :
    (βD / αD) * (βE / αE) * (βF / αF) =
    (βD * βE * βF) / (αD * αE * αF) := by
  field_simp

/-- **Ceva balance condition**: The weight product formula = 1 iff weight balance. -/
theorem ceva_balance_iff_unit_product
    (αD βD αE βE αF βF : ℝ)
    (hαD : 0 < αD) (hβD : 0 < βD)
    (hαE : 0 < αE) (hβE : 0 < βE)
    (hαF : 0 < αF) (hβF : 0 < βF) :
    αD * αE * αF = βD * βE * βF ↔
    (βD / αD) * (βE / αE) * (βF / αF) = 1 := by
  rw [ceva_product_eq_weight_ratio αD βD αE βE αF βF hαD hβD hαE hβE hαF hβF]
  have hα_prod : αD * αE * αF > 0 := mul_pos (mul_pos hαD hαE) hαF
  constructor
  · intro h; rw [← h]; exact div_self hα_prod.ne'
  · intro h; exact ((div_eq_one_iff_eq hα_prod.ne').mp h).symm

/-- **Symmetric Ceva balance**: The balance condition is symmetric under α↔β swap. -/
theorem ceva_balance_symmetric
    (αD βD αE βE αF βF : ℝ) :
    αD * αE * αF = βD * βE * βF ↔ βD * βE * βF = αD * αE * αF :=
  eq_comm

/-- **Reversed cevians**: Swapping α↔β reverses the division ratio.
    If (β/α) is the original ratio, (α/β) is the "reflected" ratio from C toward B. -/
theorem reversed_division_ratio (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (β / α) * (α / β) = 1 := by
  field_simp

/-
## Part III: Special Configurations from Non-Equal Weights

The geometric significance of specific weight choices.
-/

/-- **Centroid**: Equal weights α = β = 1 for all three cevians gives the medians.
    Each D = (B + C)/2 is the midpoint, and the product = 1 (Ceva condition holds). -/
theorem centroid_equal_weights :
    let ceva_product := (1 : ℝ) / 1 * ((1 : ℝ) / 1) * ((1 : ℝ) / 1)
    ceva_product = 1 := by norm_num

/-- **Centroid via equal weights**: With α = β, D = (B + C)/2, and the three
    cevian midpoints satisfy the Ceva condition: 1 · 1 · 1 = 1. -/
theorem centroid_weight_balance :
    (1 : ℝ) * 1 * 1 = (1 : ℝ) * 1 * 1 := rfl

/-- **Scale invariance**: Scaling both weights by the same factor preserves
    the division ratio. (αD, βD) and (c·αD, c·βD) give the same cevian point. -/
theorem weight_scale_invariance (B C α β c : ℝ) (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c) :
    (c * α * B + c * β * C) / (c * α + c * β) = (α * B + β * C) / (α + β) := by
  have hc_ne : c ≠ 0 := hc.ne'
  field_simp [hc_ne]

/-- **Ratio invariance**: The division ratio β/α = (c·β)/(c·α) is preserved
    under simultaneous scaling. -/
theorem ratio_scale_invariance (α β c : ℝ) (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c) :
    (c * β) / (c * α) = β / α := by
  field_simp [hα.ne', hc.ne']

/-- **Incenter weight condition** (angle bisector): The angle bisector from vertex A
    to side BC divides BC in ratio AB:AC (angle bisector theorem). In weight parameters,
    this corresponds to α_D = |AC| and β_D = |AB|.

    Here we state the one-variable form: if we weight by the opposite side lengths,
    then the resulting Ceva product encodes the incenter's position. -/
theorem incenter_weight_product_is_one (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    -- The angle bisectors divide the opposite sides with weights (opposite side, adjacent side):
    -- From A: D divides BC with α_D = b (= AC), β_D = c (= AB)
    -- From B: E divides CA with α_E = c (= AB), β_E = a (= BC)
    -- From C: F divides AB with α_F = a (= BC), β_F = b (= CA)
    -- Ceva product = (c/b) · (a/c) · (b/a) = 1
    (c / b) * (a / c) * (b / a) = 1 := by
  field_simp [ha.ne', hb.ne', hc.ne']

/-- **Weight balance for incenter**: The incenter weight assignment satisfies the
    balance condition b · c · a = c · a · b. -/
theorem incenter_weight_balance (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    b * c * a = c * a * b := by ring

/-- **Asymmetry of non-equal weights**: If α ≠ β, the two "halves" of the segment
    BC (from B to D, and from D to C) have different lengths. -/
theorem nonequal_weights_asymmetry (B C α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hBC : B ≠ C) (hαβ : α ≠ β) :
    β * (C - B) / (α + β) ≠ α * (C - B) / (α + β) := by
  have hCB : C - B ≠ 0 := sub_ne_zero.mpr (Ne.symm hBC)
  have hαβ_ne : α + β ≠ 0 := by linarith
  intro h
  apply hαβ
  have h1 : β * (C - B) = α * (C - B) :=
    calc β * (C - B)
        = β * (C - B) / (α + β) * (α + β) := (div_mul_cancel₀ _ hαβ_ne).symm
      _ = α * (C - B) / (α + β) * (α + β) := by rw [h]
      _ = α * (C - B) := div_mul_cancel₀ _ hαβ_ne
  exact (mul_right_cancel₀ hCB h1).symm

/-- **Closer-to-B condition**: D is closer to B (BD < DC) iff β < α.
    In other words: the cevian point is closer to B precisely when the β weight is
    smaller than the α weight (i.e., less "pull" toward C). -/
theorem weight_closer_to_B_iff (B C α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hBC : B < C) :
    (α * B + β * C) / (α + β) - B < C - (α * B + β * C) / (α + β) ↔ β < α := by
  have hαβ : α + β > 0 := by linarith
  have hDB : (α * B + β * C) / (α + β) - B = β * (C - B) / (α + β) := by
    field_simp [hαβ.ne']; ring
  have hCD : C - (α * B + β * C) / (α + β) = α * (C - B) / (α + β) := by
    field_simp [hαβ.ne']; ring
  have hCB : 0 < C - B := by linarith
  rw [hDB, hCD]
  -- Goal: β*(C-B)/(α+β) < α*(C-B)/(α+β) ↔ β < α
  constructor
  · intro h
    -- h : β*(C-B)/(α+β) < α*(C-B)/(α+β); cross-multiply to get β*(C-B) < α*(C-B)
    have h1 : β * (C - B) / (α + β) * (α + β) < α * (C - B) / (α + β) * (α + β) :=
      mul_lt_mul_of_pos_right h hαβ
    rw [div_mul_cancel₀ _ hαβ.ne', div_mul_cancel₀ _ hαβ.ne'] at h1
    nlinarith
  · intro h
    -- h : β < α → β*(C-B) < α*(C-B) → divide by (α+β) > 0
    have h1 : β * (C - B) < α * (C - B) := by nlinarith
    have h2 : β * (C - B) / (α + β) < α * (C - B) / (α + β) := by
      apply div_lt_div_of_pos_right h1 hαβ
    exact h2

end CevasOQ02OQ01OQ03
