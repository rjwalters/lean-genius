/-
  Geometric Series OQ-02 OQ-05: Toward the Holomorphic Functional Calculus

  Open Question: Extend the Neumann series to the holomorphic functional
  calculus: for holomorphic f on a neighborhood of σ(T), define
  f(T) = (2πi)⁻¹ ∮ f(z)R(z,T) dz.

  This file formalizes the resolvent of a Banach algebra element and its
  Neumann series representation — the essential bridge between the Neumann
  series (OQ-02) and spectral theory. Specifically:

  1. The resolvent R(z,a) = (z·1 - a)⁻¹ exists when ‖a‖ < ‖z‖
  2. Neumann series expansion: R(z,a) = z⁻¹ ∑ (z⁻¹·a)^n
  3. Norm bound on the resolvent
  4. First resolvent identity: R(z) - R(w) = (w-z)·R(z)·R(w)

  These results are the analytical core needed to define the Dunford-Taylor
  integral f(a) = (2πi)⁻¹ ∮ f(z)R(z,a) dz.

  References:
  - Dunford & Schwartz, "Linear Operators, Part I" (1958), VII.3
  - Rudin, "Functional Analysis" (1991), §10.4–10.6
  - Kato, "Perturbation Theory for Linear Operators" (1966), §I.5
-/

import Proofs.GeometricSeriesOQ02
import Mathlib.Analysis.Normed.Algebra.Basic

open NeumannSeries Topology Filter

noncomputable section

namespace ResolventNeumann

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [NormOneClass A]

-- ══════════════════════════════════════════════════════════════════
-- § 1. Scalar Embedding and Norm Properties
-- ══════════════════════════════════════════════════════════════════

/-- Norm of an embedded scalar in a NormOneClass algebra equals the scalar's norm. -/
theorem norm_algebraMap (z : 𝕜) : ‖algebraMap 𝕜 A z‖ = ‖z‖ := by
  rw [Algebra.algebraMap_eq_smul_one]
  rw [norm_smul]
  simp [norm_one]

/-- Embedded nonzero scalar is a unit in the algebra. -/
theorem algebraMap_isUnit {z : 𝕜} (hz : z ≠ 0) : IsUnit (algebraMap 𝕜 A z) := by
  exact (algebraMap 𝕜 A).isUnit_map (Ne.isUnit hz)

-- ══════════════════════════════════════════════════════════════════
-- § 2. The Resolvent Exists via Neumann Series
-- ══════════════════════════════════════════════════════════════════

/-- **Key norm estimate**: ‖(algebraMap z⁻¹) * a‖ < 1 when ‖a‖ < ‖z‖.

    This is the bridge from the Neumann series convergence condition ‖T‖ < 1
    to the spectral theory condition ‖a‖ < ‖z‖. -/
theorem norm_inv_smul_lt_one (a : A) {z : 𝕜} (hz : z ≠ 0) (ha : ‖a‖ < ‖z‖) :
    ‖algebraMap 𝕜 A z⁻¹ * a‖ < 1 := by
  calc ‖algebraMap 𝕜 A z⁻¹ * a‖
    _ ≤ ‖algebraMap 𝕜 A z⁻¹‖ * ‖a‖ := norm_mul_le _ _
    _ = ‖z⁻¹‖ * ‖a‖ := by rw [norm_algebraMap]
    _ = ‖z‖⁻¹ * ‖a‖ := by rw [norm_inv]
    _ < ‖z‖⁻¹ * ‖z‖ := by {
        apply mul_lt_mul_of_pos_left ha
        exact inv_pos.mpr (norm_pos_iff.mpr hz)
      }
    _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)

/-- **Factorization of z·1 - a**

    z·1 - a = (algebraMap z) * (1 - (algebraMap z⁻¹) * a)

    This algebraic identity allows us to reduce invertibility of z·1 - a
    to the Neumann series condition ‖T‖ < 1 where T = z⁻¹·a. -/
theorem resolvent_factorization (a : A) {z : 𝕜} (hz : z ≠ 0) :
    algebraMap 𝕜 A z - a =
    algebraMap 𝕜 A z * (1 - algebraMap 𝕜 A z⁻¹ * a) := by
  rw [mul_sub, mul_one, ← mul_assoc]
  congr 1
  rw [← map_mul, mul_inv_cancel₀ hz, map_one, one_mul]

/-- **Resolvent existence via Neumann series**

    For a in a Banach algebra and z with ‖a‖ < ‖z‖, the element
    (z·1 - a) is invertible. This shows z is in the resolvent set of a.

    Proof strategy: Factor z·1 - a = z·(1 - z⁻¹a). Since ‖z⁻¹a‖ < 1,
    the Neumann series shows (1 - z⁻¹a) is a unit. Since z ≠ 0,
    z·1 is also a unit. The product is therefore a unit. -/
theorem resolvent_isUnit (a : A) {z : 𝕜} (hz : z ≠ 0) (ha : ‖a‖ < ‖z‖) :
    IsUnit (algebraMap 𝕜 A z - a) := by
  rw [resolvent_factorization a hz]
  exact IsUnit.mul (algebraMap_isUnit hz) (one_sub_isUnit _ (norm_inv_smul_lt_one a hz ha))

-- ══════════════════════════════════════════════════════════════════
-- § 3. Neumann Series Representation of the Resolvent
-- ══════════════════════════════════════════════════════════════════

/-- **Summability of the resolvent series**

    The series ∑ (z⁻¹·a)^n is summable when ‖a‖ < ‖z‖. -/
theorem resolvent_series_summable (a : A) {z : 𝕜} (hz : z ≠ 0) (ha : ‖a‖ < ‖z‖) :
    Summable (fun n : ℕ => (algebraMap 𝕜 A z⁻¹ * a) ^ n) :=
  neumann_summable _ (norm_inv_smul_lt_one a hz ha)

/-- **Neumann series for the resolvent**

    Ring.inverse (z·1 - a) = (algebraMap z⁻¹) * ∑ (z⁻¹·a)^n

    This gives an explicit power series for the resolvent R(z,a),
    valid whenever ‖a‖ < ‖z‖. This is the operator-theoretic version
    of 1/(z - x) = z⁻¹ · ∑ (x/z)^n for |x| < |z|. -/
theorem resolvent_eq_neumann_series (a : A) {z : 𝕜} (hz : z ≠ 0) (ha : ‖a‖ < ‖z‖) :
    Ring.inverse (algebraMap 𝕜 A z - a) =
    algebraMap 𝕜 A z⁻¹ * ∑' n : ℕ, (algebraMap 𝕜 A z⁻¹ * a) ^ n := by
  set T := algebraMap 𝕜 A z⁻¹ * a
  have hT : ‖T‖ < 1 := norm_inv_smul_lt_one a hz ha
  rw [resolvent_factorization a hz]
  -- Use Ring.inverse (a * b) = Ring.inverse b * Ring.inverse a (when a and b commute)
  have hcomm : Commute (algebraMap 𝕜 A z) (1 - T) :=
    Algebra.commute_algebraMap_left z (1 - T)
  rw [Ring.mul_inverse_rev' hcomm]
  -- Now: Ring.inverse (1 - T) * Ring.inverse (algebraMap z) = algebraMap z⁻¹ * ∑ T^n
  -- Step 1: Ring.inverse (algebraMap z) = algebraMap z⁻¹
  have hinv_z : Ring.inverse (algebraMap 𝕜 A z) = algebraMap 𝕜 A z⁻¹ := by
    have hmul : algebraMap 𝕜 A z * algebraMap 𝕜 A z⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hz, map_one]
    have key := Ring.inverse_mul_cancel_left (algebraMap 𝕜 A z) (algebraMap 𝕜 A z⁻¹)
      (algebraMap_isUnit hz)
    rw [hmul, mul_one] at key
    exact key
  rw [hinv_z, ← neumann_sum T hT]
  -- Goal: ∑' n, T^n * algebraMap z⁻¹ = algebraMap z⁻¹ * ∑' n, T^n
  exact (Algebra.commutes z⁻¹ (∑' n, T ^ n)).symm

-- ══════════════════════════════════════════════════════════════════
-- § 4. Norm Bound on the Resolvent
-- ══════════════════════════════════════════════════════════════════

/-- **Resolvent norm bound**

    ‖R(z,a)‖ ≤ ‖z‖⁻¹ · (1 - ‖z‖⁻¹ · ‖a‖)⁻¹ = 1/(‖z‖ - ‖a‖)

    This is the quantitative bound that makes the resolvent useful
    for contour integration. As |z| → ∞, ‖R(z,a)‖ → 0. -/
theorem resolvent_norm_bound (a : A) {z : 𝕜} (hz : z ≠ 0) (ha : ‖a‖ < ‖z‖) :
    ‖Ring.inverse (algebraMap 𝕜 A z - a)‖ ≤ (‖z‖ - ‖a‖)⁻¹ := by
  set T := algebraMap 𝕜 A z⁻¹ * a
  have hT : ‖T‖ < 1 := norm_inv_smul_lt_one a hz ha
  have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have hzn : ‖z‖ ≠ 0 := ne_of_gt hzpos
  rw [resolvent_eq_neumann_series a hz ha]
  calc ‖algebraMap 𝕜 A z⁻¹ * ∑' n, T ^ n‖
    _ ≤ ‖algebraMap 𝕜 A z⁻¹‖ * ‖∑' n, T ^ n‖ := norm_mul_le _ _
    _ ≤ ‖z⁻¹‖ * (1 - ‖T‖)⁻¹ := by {
        rw [norm_algebraMap]
        exact mul_le_mul_of_nonneg_left (norm_neumann_le T hT) (norm_nonneg _)
      }
    _ = ‖z‖⁻¹ * (1 - ‖T‖)⁻¹ := by rw [norm_inv]
    _ ≤ ‖z‖⁻¹ * (1 - ‖z‖⁻¹ * ‖a‖)⁻¹ := by {
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
        have hza : ‖z‖⁻¹ * ‖a‖ < 1 :=
          calc ‖z‖⁻¹ * ‖a‖ < ‖z‖⁻¹ * ‖z‖ :=
                mul_lt_mul_of_pos_left ha (inv_pos.mpr hzpos)
            _ = 1 := inv_mul_cancel₀ hzn
        have h1za : (0 : ℝ) < 1 - ‖z‖⁻¹ * ‖a‖ := by linarith
        have hT_le : ‖T‖ ≤ ‖z‖⁻¹ * ‖a‖ :=
          calc ‖T‖ ≤ ‖algebraMap 𝕜 A z⁻¹‖ * ‖a‖ := norm_mul_le _ _
            _ = ‖z‖⁻¹ * ‖a‖ := by rw [norm_algebraMap, norm_inv]
        rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le h1za (by linarith)
      }
    _ = (‖z‖ - ‖a‖)⁻¹ := by {
        rw [show 1 - ‖z‖⁻¹ * ‖a‖ = (‖z‖ - ‖a‖) * ‖z‖⁻¹ from by
              rw [sub_mul, mul_inv_cancel₀ hzn]; ring,
            mul_inv_rev, inv_inv, ← mul_assoc,
            inv_mul_cancel₀ hzn, one_mul]
      }

-- ══════════════════════════════════════════════════════════════════
-- § 5. First Resolvent Identity (Algebraic)
-- ══════════════════════════════════════════════════════════════════

/-- **First resolvent identity**

    R(z) - R(w) = (w - z) · R(z) · R(w)

    This purely algebraic identity holds for any two points in the
    resolvent set. It is fundamental to spectral theory: it shows
    the resolvent is a "pseudo-resolvent" and implies analyticity.

    Proof: Multiply both sides by (z·1-a) on the left and (w·1-a)
    on the right, reducing to the tautology (w-z)·1 = (w-z)·1. -/
theorem first_resolvent_identity (a : A) {z w : 𝕜}
    (hz : IsUnit (algebraMap 𝕜 A z - a)) (hw : IsUnit (algebraMap 𝕜 A w - a)) :
    Ring.inverse (algebraMap 𝕜 A z - a) - Ring.inverse (algebraMap 𝕜 A w - a) =
    (algebraMap 𝕜 A w - algebraMap 𝕜 A z) *
    Ring.inverse (algebraMap 𝕜 A z - a) * Ring.inverse (algebraMap 𝕜 A w - a) := by
  -- Extract units
  obtain ⟨uz, huz⟩ := hz
  obtain ⟨uw, huw⟩ := hw
  -- Work with Ring.inverse as unit inverses
  have Rz : Ring.inverse (algebraMap 𝕜 A z - a) = ↑uz⁻¹ := by
    rw [← huz]; exact Ring.inverse_unit uz
  have Rw : Ring.inverse (algebraMap 𝕜 A w - a) = ↑uw⁻¹ := by
    rw [← huw]; exact Ring.inverse_unit uw
  rw [Rz, Rw]
  -- Key identity: uz⁻¹ - uw⁻¹ = uz⁻¹ * (uw - uz) * uw⁻¹
  -- Since uz = z·1 - a and uw = w·1 - a, we get uw - uz = (w-z)·1
  have huzw : (↑uw : A) - ↑uz = algebraMap 𝕜 A w - algebraMap 𝕜 A z := by
    rw [huw, huz]; abel
  -- The algebraic identity for unit inverses
  have key : (↑uz⁻¹ : A) - ↑uw⁻¹ = ↑uz⁻¹ * (↑uw - ↑uz) * ↑uw⁻¹ := by
    rw [mul_sub, sub_mul,
        Units.mul_inv_cancel_right (↑uz⁻¹ : A) uw,
        show (↑uz⁻¹ : A) * ↑uz * ↑uw⁻¹ = ↑uw⁻¹ from by
          rw [Units.inv_mul uz, one_mul]]
  rw [key, huzw]
  -- Goal: ↑uz⁻¹ * (algebraMap w - algebraMap z) * ↑uw⁻¹ = (algebraMap w - algebraMap z) * ↑uz⁻¹ * ↑uw⁻¹
  -- The scalar (algebraMap w - algebraMap z) commutes with everything
  rw [← map_sub (algebraMap 𝕜 A)]
  rw [← Algebra.commutes (w - z) (↑uz⁻¹ : A)]

-- ══════════════════════════════════════════════════════════════════
-- § 6. Resolvent Vanishes at Infinity
-- ══════════════════════════════════════════════════════════════════

/-- **Resolvent vanishes at infinity**

    ‖R(z,a)‖ ≤ 1/(‖z‖ - ‖a‖) → 0 as ‖z‖ → ∞.

    This is essential for the holomorphic functional calculus:
    it ensures that ∮ f(z)R(z,a) dz converges when the contour
    is sufficiently large and f is bounded. -/
theorem resolvent_tendsto_zero (a : A) :
    Filter.Tendsto (fun z : 𝕜 => Ring.inverse (algebraMap 𝕜 A z - a))
    (Filter.comap (fun z => ‖z‖) Filter.atTop) (nhds 0) := by
  apply squeeze_zero_norm'
  · -- Eventually ‖R(z,a)‖ ≤ (‖z‖ - ‖a‖)⁻¹
    rw [Filter.eventually_iff, Filter.mem_comap]
    refine ⟨{r : ℝ | ‖a‖ + 1 ≤ r}, Filter.mem_atTop _, fun z hz => ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hz
    have hpos : 0 < ‖z‖ := by linarith [norm_nonneg a]
    exact resolvent_norm_bound a (norm_pos_iff.mp hpos) (by linarith)
  · -- (‖z‖ - ‖a‖)⁻¹ → 0 as ‖z‖ → ∞
    have h_sub : Filter.Tendsto (fun r : ℝ => r - ‖a‖) Filter.atTop Filter.atTop := by
      intro s hs
      obtain ⟨b, hb⟩ := Filter.mem_atTop_sets.mp hs
      apply Filter.mem_atTop_sets.mpr
      exact ⟨b + ‖a‖, fun r hr => hb _ (by linarith)⟩
    exact (tendsto_inv_atTop_zero.comp h_sub).comp Filter.tendsto_comap

end ResolventNeumann
