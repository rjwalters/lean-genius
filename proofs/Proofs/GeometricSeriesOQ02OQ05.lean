/-
  Geometric Series OQ-02 OQ-05: Toward the Holomorphic Functional Calculus

  Open Question: Extend the Neumann series to the holomorphic functional
  calculus: for holomorphic f on a neighborhood of σ(T), define
  f(T) = (2πi)⁻¹ ∮ f(λ)R(λ,T) dλ.

  This file formalizes the resolvent of a Banach algebra element and its
  Neumann series representation — the essential bridge between the Neumann
  series (OQ-02) and spectral theory. Specifically:

  1. The resolvent R(λ,a) = (λ·1 - a)⁻¹ exists when ‖a‖ < ‖λ‖
  2. Neumann series expansion: R(λ,a) = λ⁻¹ ∑ (λ⁻¹·a)^n
  3. Norm bound on the resolvent
  4. First resolvent identity: R(λ) - R(μ) = (μ-λ)·R(λ)·R(μ)

  These results are the analytical core needed to define the Dunford-Taylor
  integral f(a) = (2πi)⁻¹ ∮ f(λ)R(λ,a) dλ.

  References:
  - Dunford & Schwartz, "Linear Operators, Part I" (1958), VII.3
  - Rudin, "Functional Analysis" (1991), §10.4–10.6
  - Kato, "Perturbation Theory for Linear Operators" (1966), §I.5
-/

import Proofs.GeometricSeriesOQ02
import Mathlib.Analysis.NormedSpace.Basic

open NeumannSeries Topology Filter

noncomputable section

namespace ResolventNeumann

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [NormOneClass A]

-- ══════════════════════════════════════════════════════════════════
-- § 1. Scalar Embedding and Norm Properties
-- ══════════════════════════════════════════════════════════════════

/-- Norm of an embedded scalar in a NormOneClass algebra equals the scalar's norm. -/
theorem norm_algebraMap (λ : 𝕜) : ‖algebraMap 𝕜 A λ‖ = ‖λ‖ := by
  rw [Algebra.algebraMap_eq_smul_one]
  rw [norm_smul]
  simp [norm_one]

/-- Embedded nonzero scalar is a unit in the algebra. -/
theorem algebraMap_isUnit {λ : 𝕜} (hλ : λ ≠ 0) : IsUnit (algebraMap 𝕜 A λ) := by
  exact (algebraMap 𝕜 A).isUnit_map (Ne.isUnit hλ)

-- ══════════════════════════════════════════════════════════════════
-- § 2. The Resolvent Exists via Neumann Series
-- ══════════════════════════════════════════════════════════════════

/-- **Key norm estimate**: ‖(algebraMap λ⁻¹) * a‖ < 1 when ‖a‖ < ‖λ‖.

    This is the bridge from the Neumann series convergence condition ‖T‖ < 1
    to the spectral theory condition ‖a‖ < ‖λ‖. -/
theorem norm_inv_smul_lt_one (a : A) {λ : 𝕜} (hλ : λ ≠ 0) (ha : ‖a‖ < ‖λ‖) :
    ‖algebraMap 𝕜 A λ⁻¹ * a‖ < 1 := by
  calc ‖algebraMap 𝕜 A λ⁻¹ * a‖
    _ ≤ ‖algebraMap 𝕜 A λ⁻¹‖ * ‖a‖ := norm_mul_le _ _
    _ = ‖λ⁻¹‖ * ‖a‖ := by rw [norm_algebraMap]
    _ = ‖λ‖⁻¹ * ‖a‖ := by rw [norm_inv]
    _ < ‖λ‖⁻¹ * ‖λ‖ := by {
        apply mul_lt_mul_of_pos_left ha
        exact inv_pos.mpr (norm_pos_iff.mpr hλ)
      }
    _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr hλ)

/-- **Factorization of λ·1 - a**

    λ·1 - a = (algebraMap λ) * (1 - (algebraMap λ⁻¹) * a)

    This algebraic identity allows us to reduce invertibility of λ·1 - a
    to the Neumann series condition ‖T‖ < 1 where T = λ⁻¹·a. -/
theorem resolvent_factorization (a : A) {λ : 𝕜} (hλ : λ ≠ 0) :
    algebraMap 𝕜 A λ - a =
    algebraMap 𝕜 A λ * (1 - algebraMap 𝕜 A λ⁻¹ * a) := by
  rw [mul_sub, mul_one, ← mul_assoc]
  congr 1
  rw [← map_mul, mul_inv_cancel₀ hλ, map_one]

/-- **Resolvent existence via Neumann series**

    For a in a Banach algebra and λ with ‖a‖ < ‖λ‖, the element
    (λ·1 - a) is invertible. This shows λ is in the resolvent set of a.

    Proof strategy: Factor λ·1 - a = λ·(1 - λ⁻¹a). Since ‖λ⁻¹a‖ < 1,
    the Neumann series shows (1 - λ⁻¹a) is a unit. Since λ ≠ 0,
    λ·1 is also a unit. The product is therefore a unit. -/
theorem resolvent_isUnit (a : A) {λ : 𝕜} (hλ : λ ≠ 0) (ha : ‖a‖ < ‖λ‖) :
    IsUnit (algebraMap 𝕜 A λ - a) := by
  rw [resolvent_factorization a hλ]
  exact IsUnit.mul (algebraMap_isUnit hλ) (one_sub_isUnit _ (norm_inv_smul_lt_one a hλ ha))

-- ══════════════════════════════════════════════════════════════════
-- § 3. Neumann Series Representation of the Resolvent
-- ══════════════════════════════════════════════════════════════════

/-- **Summability of the resolvent series**

    The series ∑ (λ⁻¹·a)^n is summable when ‖a‖ < ‖λ‖. -/
theorem resolvent_series_summable (a : A) {λ : 𝕜} (hλ : λ ≠ 0) (ha : ‖a‖ < ‖λ‖) :
    Summable (fun n : ℕ => (algebraMap 𝕜 A λ⁻¹ * a) ^ n) :=
  neumann_summable _ (norm_inv_smul_lt_one a hλ ha)

/-- **Neumann series for the resolvent**

    Ring.inverse (λ·1 - a) = (algebraMap λ⁻¹) * ∑ (λ⁻¹·a)^n

    This gives an explicit power series for the resolvent R(λ,a),
    valid whenever ‖a‖ < ‖λ‖. This is the operator-theoretic version
    of 1/(λ - x) = λ⁻¹ · ∑ (x/λ)^n for |x| < |λ|. -/
theorem resolvent_eq_neumann_series (a : A) {λ : 𝕜} (hλ : λ ≠ 0) (ha : ‖a‖ < ‖λ‖) :
    Ring.inverse (algebraMap 𝕜 A λ - a) =
    algebraMap 𝕜 A λ⁻¹ * ∑' n : ℕ, (algebraMap 𝕜 A λ⁻¹ * a) ^ n := by
  set T := algebraMap 𝕜 A λ⁻¹ * a
  have hT : ‖T‖ < 1 := norm_inv_smul_lt_one a hλ ha
  -- Ring.inverse (λ·(1 - T)) = Ring.inverse (1 - T) * Ring.inverse (λ·1)
  rw [resolvent_factorization a hλ]
  -- Ring.inverse of product of units
  have hλ_unit := algebraMap_isUnit (A := A) hλ
  have h1T_unit := one_sub_isUnit T hT
  -- Ring.inverse (λ * (1 - T)) where both are units
  rw [Ring.inverse_unit (hλ_unit.mul h1T_unit)]
  -- ↑(u * v)⁻¹ = ↑v⁻¹ * ↑u⁻¹
  simp only [Units.val_mul, IsUnit.val_inv_mul]
  rw [mul_comm (Ring.inverse (1 - T)) (Ring.inverse (algebraMap 𝕜 A λ))]
  congr 1
  · -- Ring.inverse (algebraMap λ) = algebraMap λ⁻¹
    rw [Ring.inverse_unit hλ_unit]
    simp [IsUnit.unit, Units.val_inv_eq_inv_val]
    rw [← map_inv₀]
  · -- Ring.inverse (1 - T) = ∑ T^n
    exact neumann_sum T hT

-- ══════════════════════════════════════════════════════════════════
-- § 4. Norm Bound on the Resolvent
-- ══════════════════════════════════════════════════════════════════

/-- **Resolvent norm bound**

    ‖R(λ,a)‖ ≤ ‖λ‖⁻¹ · (1 - ‖λ‖⁻¹ · ‖a‖)⁻¹ = 1/(‖λ‖ - ‖a‖)

    This is the quantitative bound that makes the resolvent useful
    for contour integration. As |λ| → ∞, ‖R(λ,a)‖ → 0. -/
theorem resolvent_norm_bound (a : A) {λ : 𝕜} (hλ : λ ≠ 0) (ha : ‖a‖ < ‖λ‖) :
    ‖Ring.inverse (algebraMap 𝕜 A λ - a)‖ ≤ (‖λ‖ - ‖a‖)⁻¹ := by
  set T := algebraMap 𝕜 A λ⁻¹ * a
  have hT : ‖T‖ < 1 := norm_inv_smul_lt_one a hλ ha
  rw [resolvent_eq_neumann_series a hλ ha]
  calc ‖algebraMap 𝕜 A λ⁻¹ * ∑' n, T ^ n‖
    _ ≤ ‖algebraMap 𝕜 A λ⁻¹‖ * ‖∑' n, T ^ n‖ := norm_mul_le _ _
    _ ≤ ‖λ⁻¹‖ * (1 - ‖T‖)⁻¹ := by {
        apply mul_le_mul_of_nonneg_left (norm_neumann_le T hT)
        rw [norm_algebraMap]; exact le_refl _
      }
    _ = ‖λ‖⁻¹ * (1 - ‖T‖)⁻¹ := by rw [norm_inv]
    _ ≤ ‖λ‖⁻¹ * (1 - ‖λ‖⁻¹ * ‖a‖)⁻¹ := by {
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
        apply inv_anti_of_pos
        · linarith [norm_inv_smul_lt_one a hλ ha]
        · calc 1 - ‖λ‖⁻¹ * ‖a‖
            _ ≤ 1 - ‖T‖ := by {
                apply sub_le_sub_left
                calc ‖T‖ ≤ ‖algebraMap 𝕜 A λ⁻¹‖ * ‖a‖ := norm_mul_le _ _
                _ = ‖λ‖⁻¹ * ‖a‖ := by rw [norm_algebraMap, norm_inv]
              }
      }
    _ = (‖λ‖ - ‖a‖)⁻¹ := by {
        rw [show (1 - ‖λ‖⁻¹ * ‖a‖) = (‖λ‖ - ‖a‖) / ‖λ‖ from by
          field_simp]
        rw [inv_div, mul_div_cancel₀]
        exact norm_ne_zero_iff.mpr hλ
      }

-- ══════════════════════════════════════════════════════════════════
-- § 5. First Resolvent Identity (Algebraic)
-- ══════════════════════════════════════════════════════════════════

/-- **First resolvent identity**

    R(λ) - R(μ) = (μ - λ) · R(λ) · R(μ)

    This purely algebraic identity holds for any two points in the
    resolvent set. It is fundamental to spectral theory: it shows
    the resolvent is a "pseudo-resolvent" and implies analyticity.

    Proof: Multiply both sides by (λ·1-a) on the left and (μ·1-a)
    on the right, reducing to the tautology (μ-λ)·1 = (μ-λ)·1. -/
theorem first_resolvent_identity (a : A) {λ μ : 𝕜}
    (hλ : IsUnit (algebraMap 𝕜 A λ - a)) (hμ : IsUnit (algebraMap 𝕜 A μ - a)) :
    Ring.inverse (algebraMap 𝕜 A λ - a) - Ring.inverse (algebraMap 𝕜 A μ - a) =
    (algebraMap 𝕜 A μ - algebraMap 𝕜 A λ) *
    Ring.inverse (algebraMap 𝕜 A λ - a) * Ring.inverse (algebraMap 𝕜 A μ - a) := by
  -- Extract units
  obtain ⟨uλ, huλ⟩ := hλ
  obtain ⟨uμ, huμ⟩ := hμ
  -- Work with Ring.inverse as unit inverses
  have Rλ : Ring.inverse (algebraMap 𝕜 A λ - a) = ↑uλ⁻¹ := by
    rw [← huλ]; exact Ring.inverse_unit uλ
  have Rμ : Ring.inverse (algebraMap 𝕜 A μ - a) = ↑uμ⁻¹ := by
    rw [← huμ]; exact Ring.inverse_unit uμ
  rw [Rλ, Rμ]
  -- Key identity: uλ⁻¹ - uμ⁻¹ = uλ⁻¹ * (uμ - uλ) * uμ⁻¹
  -- Since uλ = λ·1 - a and uμ = μ·1 - a, we get uμ - uλ = (μ-λ)·1
  have huλμ : (↑uμ : A) - ↑uλ = algebraMap 𝕜 A μ - algebraMap 𝕜 A λ := by
    rw [← huμ, ← huλ]; ring
  -- The algebraic identity for unit inverses
  have key : (↑uλ⁻¹ : A) - ↑uμ⁻¹ = ↑uλ⁻¹ * (↑uμ - ↑uλ) * ↑uμ⁻¹ := by
    have := Units.val_inv_mul uλ
    have := Units.val_inv_mul uμ
    rw [show (↑uλ⁻¹ : A) - ↑uμ⁻¹ =
        ↑uλ⁻¹ * (↑uμ * ↑uμ⁻¹) - (↑uλ⁻¹ * ↑uλ) * ↑uμ⁻¹ from by
      simp [Units.mul_inv_cancel_right, Units.inv_mul_cancel_right]]
    ring
  rw [key, huλμ]

-- ══════════════════════════════════════════════════════════════════
-- § 6. Resolvent Vanishes at Infinity
-- ══════════════════════════════════════════════════════════════════

/-- **Resolvent vanishes at infinity**

    ‖R(λ,a)‖ ≤ 1/(‖λ‖ - ‖a‖) → 0 as ‖λ‖ → ∞.

    This is essential for the holomorphic functional calculus:
    it ensures that ∮ f(λ)R(λ,a) dλ converges when the contour
    is sufficiently large and f is bounded. -/
theorem resolvent_tendsto_zero (a : A) :
    Filter.Tendsto (fun λ : 𝕜 => Ring.inverse (algebraMap 𝕜 A λ - a))
    (Filter.comap (fun λ => ‖λ‖) Filter.atTop) (nhds 0) := by
  -- Strategy: for ‖λ‖ ≥ ε⁻¹ + ‖a‖ + 1, apply resolvent_norm_bound then
  -- use (‖λ‖ - ‖a‖)⁻¹ < (ε⁻¹)⁻¹ = ε via strict antitone of inv.
  rw [Metric.tendsto_nhds]
  intro ε hε
  simp only [dist_zero_right]
  rw [Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨ε⁻¹ + ‖a‖ + 1, fun r hr λ hλr => ?_⟩
  -- hr : ε⁻¹ + ‖a‖ + 1 ≤ r,  hλr : ‖λ‖ = r
  have hλ_ne : λ ≠ 0 := by
    intro h; rw [h, norm_zero] at hλr
    linarith [hλr.symm.le, norm_nonneg a, inv_pos.mpr hε]
  have ha_lt : ‖a‖ < ‖λ‖ := by
    linarith [hλr.symm.le, inv_pos.mpr hε, norm_nonneg a]
  have h_pos : (0 : ℝ) < ‖λ‖ - ‖a‖ := by linarith
  have hd : ε⁻¹ < ‖λ‖ - ‖a‖ := by linarith [hλr.symm.le, norm_nonneg a]
  calc ‖Ring.inverse (algebraMap 𝕜 A λ - a)‖
    _ ≤ (‖λ‖ - ‖a‖)⁻¹ := resolvent_norm_bound a hλ_ne ha_lt
    _ < ε := by
        calc (‖λ‖ - ‖a‖)⁻¹
            < (ε⁻¹)⁻¹ := inv_lt_inv_of_lt (inv_pos.mpr hε) hd
          _ = ε := inv_inv ε

end ResolventNeumann
