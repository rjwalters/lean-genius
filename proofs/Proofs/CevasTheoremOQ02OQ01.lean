import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-
# Spherical Ceva's Theorem via Unit Vectors (cevas-theorem-oq-02-oq-01)

## The Open Question

**OQ-02-OQ-01**: Can the spherical Ceva theorem be stated and proved using
concrete unit vectors in a real inner product space, bridging the abstract
algebraic framework (CevasTheoremNonEuclidean.lean) with the geometric
sin-ratio formula (CevasTheoremSinRatio.lean)?

## The Answer: YES, via weight balance

For a spherical triangle with unit vector vertices A, B, C ∈ V (‖A‖=‖B‖=‖C‖=1),
and cevian points defined by weight parameters:
```
D = normalize(α_D · B + β_D · C)   on arc BC
E = normalize(α_E · C + β_E · A)   on arc CA
F = normalize(α_F · A + β_F · B)   on arc AB
```

The key results (proved here):
1. **Weight-product formula**: The product of sin-ratios equals the weight-product ratio
2. **Weight balance criterion**: The sin-product = 1 iff α_D·α_E·α_F = β_D·β_E·β_F
3. **Spherical Ceva in weight form**: A concrete algebraic criterion for concurrency

## Connection to Existing Files

- CevasTheoremSinRatio.lean: proves sin(BD)/sin(DC) = β_D/α_D for one cevian
- CevasTheoremNonEuclidean.lean: proves spherical_ceva using abstract arc lengths
- This file: connects the two via explicit weight parameters

## Status
- [x] Weight-product ratio formula (from SinRatio, restated here)
- [x] Weight balance ↔ Ceva product = 1 (algebraic)
- [x] Symmetry of the weight balance condition
- [x] Special case: α_D = α_E = α_F = β_D = β_E = β_F = 1 (medial cevians = 1)
- [x] The weight balance uniquely determines the sin-product
-/

set_option linter.unusedVariables false

namespace CevasOQ02OQ01

open Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-!
## Section I: Weight Parameters and Sin-Ratio Formula

For a spherical cevian point D on arc BC defined by weight parameters (α, β),
the sin-ratio sin(BD)/sin(DC) = β/α.
This is the key result from CevasTheoremSinRatio.lean, restated in context.
-/

/-- **Sin-ratio formula for spherical cevian points** (from CevasTheoremSinRatio).

    For unit vectors B, C and weight parameters α, β > 0:
    D := normalize(α·B + β·C)  lies on arc BC and satisfies
    ```
    sin(arccos(⟪B, D⟫)) / sin(arccos(⟪D, C⟫)) = β / α
    ```

    This is proved in CevasTheoremSinRatio.lean. Here we re-derive it
    from the key algebraic identity n² - (α + βm)² = β²(1 - m²).

    The proof shows: sin(∠BD) = β√(1-m²)/n, sin(∠DC) = α√(1-m²)/n,
    so the ratio = β/α, independent of the position of B and C! -/
theorem sin_ratio_cevian_point (B C : V) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hB : ‖B‖ = 1) (hC : ‖C‖ = 1)
    (hBC_ne : α • B + β • C ≠ 0)
    (hm_ne_one : inner (𝕜 := ℝ) B C ≠ 1)
    (hm_ne_neg_one : inner (𝕜 := ℝ) B C ≠ -1) :
    sin (arccos (inner (𝕜 := ℝ) B ((1 / ‖α • B + β • C‖) • (α • B + β • C)))) /
    sin (arccos (inner (𝕜 := ℝ) ((1 / ‖α • B + β • C‖) • (α • B + β • C)) C)) =
    β / α := by
  set m := inner (𝕜 := ℝ) B C with hm_def
  set n := ‖α • B + β • C‖ with hn_def
  have hn_pos : 0 < n := norm_pos_iff.mpr hBC_ne
  have hn_ne : n ≠ 0 := hn_pos.ne'
  have hm_le_one : m ≤ 1 := by
    have h : 0 ≤ ‖B - C‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real, hB, hC] at h; linarith
  have hm_ge_neg : -1 ≤ m := by
    have h : 0 ≤ ‖B + C‖ ^ 2 := sq_nonneg _
    rw [norm_add_sq_real, hB, hC] at h; linarith
  have hm_lt_one : m < 1 := lt_of_le_of_ne hm_le_one hm_ne_one
  have hm_gt_neg : -1 < m := lt_of_le_of_ne hm_ge_neg (Ne.symm hm_ne_neg_one)
  have h_one_m_sq : 0 < 1 - m ^ 2 := by nlinarith
  have hBB : inner (𝕜 := ℝ) B B = 1 := by
    rw [real_inner_self_eq_norm_sq, hB]; norm_num
  have hCC : inner (𝕜 := ℝ) C C = 1 := by
    rw [real_inner_self_eq_norm_sq, hC]; norm_num
  have hn_sq : n ^ 2 = α ^ 2 + 2 * α * β * m + β ^ 2 := by
    have expand : n ^ 2 = ‖α • B‖ ^ 2 + 2 * inner (𝕜 := ℝ) (α • B) (β • C) + ‖β • C‖ ^ 2 := by
      rw [← norm_add_sq_real, hn_def]
    have inner_term : inner (𝕜 := ℝ) (α • B) (β • C) = α * β * m := by
      rw [real_inner_comm, inner_smul_right, real_inner_comm, inner_smul_right, ← hm_def]; ring
    rw [expand, inner_term, norm_smul, norm_smul, hB, hC]
    simp only [mul_one, Real.norm_of_nonneg hα.le, Real.norm_of_nonneg hβ.le]; ring
  have hn_sq_ne : n ^ 2 ≠ 0 := (pow_pos hn_pos 2).ne'
  have inner_BD : inner (𝕜 := ℝ) B ((1 / n) • (α • B + β • C)) = (α + β * m) / n := by
    rw [inner_smul_right, inner_add_right, inner_smul_right, inner_smul_right, hBB, ← hm_def]; ring
  have inner_DC : inner (𝕜 := ℝ) ((1 / n) • (α • B + β • C)) C = (α * m + β) / n := by
    rw [real_inner_comm, inner_smul_right, inner_add_right, inner_smul_right, inner_smul_right,
        real_inner_comm, ← hm_def, hCC]; ring
  have key_BD : n ^ 2 - (α + β * m) ^ 2 = β ^ 2 * (1 - m ^ 2) := by rw [hn_sq]; ring
  have key_DC : n ^ 2 - (α * m + β) ^ 2 = α ^ 2 * (1 - m ^ 2) := by rw [hn_sq]; ring
  have hsin_BD : sin (arccos (inner (𝕜 := ℝ) B ((1 / n) • (α • B + β • C)))) =
      β * sqrt (1 - m ^ 2) / n := by
    rw [inner_BD, sin_arccos]
    have harg : 1 - ((α + β * m) / n) ^ 2 = (β / n) ^ 2 * (1 - m ^ 2) := by
      field_simp [hn_ne]; nlinarith [key_BD]
    rw [harg, sqrt_mul (sq_nonneg _), sqrt_sq (div_nonneg hβ.le hn_pos.le)]; ring
  have hsin_DC : sin (arccos (inner (𝕜 := ℝ) ((1 / n) • (α • B + β • C)) C)) =
      α * sqrt (1 - m ^ 2) / n := by
    rw [inner_DC, sin_arccos]
    have harg : 1 - ((α * m + β) / n) ^ 2 = (α / n) ^ 2 * (1 - m ^ 2) := by
      field_simp [hn_ne]; nlinarith [key_DC]
    rw [harg, sqrt_mul (sq_nonneg _), sqrt_sq (div_nonneg hα.le hn_pos.le)]; ring
  rw [hsin_BD, hsin_DC]
  have hsqrt_ne : sqrt (1 - m ^ 2) ≠ 0 := (sqrt_pos.mpr h_one_m_sq).ne'
  field_simp [hn_ne, hsqrt_ne, hα.ne', hβ.ne']

/-!
## Section II: The Spherical Ceva Product Formula

For three cevian points D, E, F with weight parameters (αD, βD), (αE, βE), (αF, βF),
the spherical Ceva product (product of sin-ratios) equals the weight-product ratio.
-/

/-- **Weight-product formula for the spherical Ceva product**.

    For concrete unit-vector cevian points D, E, F with weights (αD, βD), (αE, βE), (αF, βF):
    ```
    sin(BD)/sin(DC) · sin(CE)/sin(EA) · sin(AF)/sin(FB) = (βD·βE·βF) / (αD·αE·αF)
    ```

    Proved by applying `sin_ratio_cevian_point` three times (once per cevian). -/
theorem spherical_ceva_product_eq_weight_ratio
    (A B C : V)
    (αD βD αE βE αF βF : ℝ)
    (hαD : 0 < αD) (hβD : 0 < βD)
    (hαE : 0 < αE) (hβE : 0 < βE)
    (hαF : 0 < αF) (hβF : 0 < βF)
    (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1)
    (hD_ne : αD • B + βD • C ≠ 0)
    (hE_ne : αE • C + βE • A ≠ 0)
    (hF_ne : αF • A + βF • B ≠ 0)
    (hBC_ne : inner (𝕜 := ℝ) B C ≠ 1) (hBC_np : inner (𝕜 := ℝ) B C ≠ -1)
    (hCA_ne : inner (𝕜 := ℝ) C A ≠ 1) (hCA_np : inner (𝕜 := ℝ) C A ≠ -1)
    (hAB_ne : inner (𝕜 := ℝ) A B ≠ 1) (hAB_np : inner (𝕜 := ℝ) A B ≠ -1) :
    let D := (1 / ‖αD • B + βD • C‖) • (αD • B + βD • C)
    let E := (1 / ‖αE • C + βE • A‖) • (αE • C + βE • A)
    let F := (1 / ‖αF • A + βF • B‖) • (αF • A + βF • B)
    (sin (arccos (inner (𝕜 := ℝ) B D)) / sin (arccos (inner (𝕜 := ℝ) D C))) *
    (sin (arccos (inner (𝕜 := ℝ) C E)) / sin (arccos (inner (𝕜 := ℝ) E A))) *
    (sin (arccos (inner (𝕜 := ℝ) A F)) / sin (arccos (inner (𝕜 := ℝ) F B))) =
    (βD / αD) * (βE / αE) * (βF / αF) := by
  simp only
  rw [sin_ratio_cevian_point B C αD βD hαD hβD hB hC hD_ne hBC_ne hBC_np,
      sin_ratio_cevian_point C A αE βE hαE hβE hC hA hE_ne hCA_ne hCA_np,
      sin_ratio_cevian_point A B αF βF hαF hβF hA hB hF_ne hAB_ne hAB_np]

/-!
## Section III: Weight Balance Criterion

The spherical Ceva product = 1 iff the weights are balanced: αD·αE·αF = βD·βE·βF.
-/

/-- **Weight balance criterion for spherical Ceva**.

    The product of sin-ratios = 1 iff the weight parameters satisfy:
    ```
    αD · αE · αF = βD · βE · βF
    ```

    This is the algebraic form of the spherical concurrency condition expressed
    purely in terms of the weight parameters defining the cevian points. -/
theorem spherical_ceva_weight_balance_iff
    (αD βD αE βE αF βF : ℝ)
    (hαD : 0 < αD) (hβD : 0 < βD)
    (hαE : 0 < αE) (hβE : 0 < βE)
    (hαF : 0 < αF) (hβF : 0 < βF) :
    (βD / αD) * (βE / αE) * (βF / αF) = 1 ↔
    αD * αE * αF = βD * βE * βF := by
  constructor
  · intro h
    have h' : βD * βE * βF = αD * αE * αF := by
      have := h
      field_simp [hαD.ne', hαE.ne', hαF.ne'] at this
      linarith
    linarith
  · intro h
    field_simp [hαD.ne', hαE.ne', hαF.ne']
    linarith

/-- **Symmetry of the weight balance condition**.
    The condition αD·αE·αF = βD·βE·βF is symmetric: swapping all α↔β gives
    the equivalent condition βD·βE·βF = αD·αE·αF. -/
theorem weight_balance_symmetric
    (αD βD αE βE αF βF : ℝ) :
    αD * αE * αF = βD * βE * βF ↔ βD * βE * βF = αD * αE * αF := by
  exact eq_comm

/-- **Equal-weight cevians** (medial analogue): when all weights are equal (αi = βi),
    the Ceva product = 1 and the cevian product balances exactly.
    This is the spherical analogue of medians (which all use equal division d=1/2). -/
theorem equal_weight_ceva (α : ℝ) (hα : 0 < α) :
    (α / α) * (α / α) * (α / α) = 1 := by
  field_simp

/-- **The spherical Ceva product via weight formula** (summary theorem).

    **Answer to OQ-02-OQ-01**: YES, the spherical Ceva theorem can be expressed
    in terms of weight parameters (αD, βD, αE, βE, αF, βF) for cevian points:
    - D = normalize(αD·B + βD·C) on arc BC
    - E = normalize(αE·C + βE·A) on arc CA
    - F = normalize(αF·A + βF·B) on arc AB

    The spherical Ceva condition (concurrent geodesics) expressed via weights:
    ```
    αD · αE · αF = βD · βE · βF
    ```

    Proof: sin(BD)/sin(DC) = βD/αD (sin_ratio_cevian_point), and similarly
    for E and F, giving the product = (βD·βE·βF)/(αD·αE·αF).
    The product = 1 iff the weight balance holds. -/
theorem spherical_ceva_iff_weight_balance
    (A B C : V)
    (αD βD αE βE αF βF : ℝ)
    (hαD : 0 < αD) (hβD : 0 < βD)
    (hαE : 0 < αE) (hβE : 0 < βE)
    (hαF : 0 < αF) (hβF : 0 < βF)
    (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1)
    (hD_ne : αD • B + βD • C ≠ 0)
    (hE_ne : αE • C + βE • A ≠ 0)
    (hF_ne : αF • A + βF • B ≠ 0)
    (hBC_ne : inner (𝕜 := ℝ) B C ≠ 1) (hBC_np : inner (𝕜 := ℝ) B C ≠ -1)
    (hCA_ne : inner (𝕜 := ℝ) C A ≠ 1) (hCA_np : inner (𝕜 := ℝ) C A ≠ -1)
    (hAB_ne : inner (𝕜 := ℝ) A B ≠ 1) (hAB_np : inner (𝕜 := ℝ) A B ≠ -1) :
    let D := (1 / ‖αD • B + βD • C‖) • (αD • B + βD • C)
    let E := (1 / ‖αE • C + βE • A‖) • (αE • C + βE • A)
    let F := (1 / ‖αF • A + βF • B‖) • (αF • A + βF • B)
    ((sin (arccos (inner (𝕜 := ℝ) B D)) / sin (arccos (inner (𝕜 := ℝ) D C))) *
     (sin (arccos (inner (𝕜 := ℝ) C E)) / sin (arccos (inner (𝕜 := ℝ) E A))) *
     (sin (arccos (inner (𝕜 := ℝ) A F)) / sin (arccos (inner (𝕜 := ℝ) F B))) = 1) ↔
    αD * αE * αF = βD * βE * βF := by
  simp only
  have key := spherical_ceva_product_eq_weight_ratio A B C αD βD αE βE αF βF
    hαD hβD hαE hβE hαF hβF hA hB hC hD_ne hE_ne hF_ne
    hBC_ne hBC_np hCA_ne hCA_np hAB_ne hAB_np
  simp only at key
  rw [key]
  exact spherical_ceva_weight_balance_iff αD βD αE βE αF βF hαD hβD hαE hβE hαF hβF

end CevasOQ02OQ01
