/-
  Geometric Series OQ-02 OQ-05: Toward the Holomorphic Functional Calculus

  Open Question: Extend the Neumann series to the holomorphic functional
  calculus: for holomorphic f on a neighborhood of σ(T), define
  f(T) = (2πi)⁻¹ ∮ f(lam)R(lam,T) dlam.

  This file formalizes the resolvent of a Banach algebra element and its
  Neumann series representation — the essential bridge between the Neumann
  series (OQ-02) and spectral theory. Specifically:

  1. The resolvent R(lam,a) = (lam·1 - a)⁻¹ exists when ‖a‖ < ‖lam‖
  2. Neumann series expansion: R(lam,a) = lam⁻¹ ∑ (lam⁻¹·a)^n
  3. Norm bound on the resolvent
  4. First resolvent identity: R(lam) - R(μ) = (μ-lam)·R(lam)·R(μ)

  These results are the analytical core needed to define the Dunford-Taylor
  integral f(a) = (2πi)⁻¹ ∮ f(lam)R(lam,a) dlam.

  References:
  - Dunford & Schwartz, "Linear Operators, Part I" (1958), VII.3
  - Rudin, "Functional Analysis" (1991), §10.4–10.6
  - Kato, "Perturbation Theory for Linear Operators" (1966), §I.5
-/

import Proofs.GeometricSeriesOQ02
import Mathlib

open NeumannSeries Topology Filter

noncomputable section

namespace ResolventNeumann

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [NormOneClass A]

-- ══════════════════════════════════════════════════════════════════
-- § 1. Scalar Embedding and Norm Properties
-- ══════════════════════════════════════════════════════════════════

/-- Norm of an embedded scalar in a NormOneClass algebra equals the scalar's norm. -/
theorem norm_algebraMap (lam : 𝕜) : ‖algebraMap 𝕜 A lam‖ = ‖lam‖ := by
  rw [Algebra.algebraMap_eq_smul_one]
  rw [norm_smul]
  simp [norm_one]

/-- Embedded nonzero scalar is a unit in the algebra. -/
theorem algebraMap_isUnit {lam : 𝕜} (hlam : lam ≠ 0) : IsUnit (algebraMap 𝕜 A lam) := by
  exact (algebraMap 𝕜 A).isUnit_map (Ne.isUnit hlam)

-- ══════════════════════════════════════════════════════════════════
-- § 2. The Resolvent Exists via Neumann Series
-- ══════════════════════════════════════════════════════════════════

/-- **Key norm estimate**: ‖(algebraMap lam⁻¹) * a‖ < 1 when ‖a‖ < ‖lam‖.

    This is the bridge from the Neumann series convergence condition ‖T‖ < 1
    to the spectral theory condition ‖a‖ < ‖lam‖. -/
theorem norm_inv_smul_lt_one (a : A) {lam : 𝕜} (hlam : lam ≠ 0) (ha : ‖a‖ < ‖lam‖) :
    ‖algebraMap 𝕜 A lam⁻¹ * a‖ < 1 := by
  calc ‖algebraMap 𝕜 A lam⁻¹ * a‖
    _ ≤ ‖algebraMap 𝕜 A lam⁻¹‖ * ‖a‖ := norm_mul_le _ _
    _ = ‖lam⁻¹‖ * ‖a‖ := by rw [norm_algebraMap]
    _ = ‖lam‖⁻¹ * ‖a‖ := by rw [norm_inv]
    _ < ‖lam‖⁻¹ * ‖lam‖ := by {
        apply mul_lt_mul_of_pos_left ha
        exact inv_pos.mpr (norm_pos_iff.mpr hlam)
      }
    _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr hlam)

/-- **Factorization of lam·1 - a**

    lam·1 - a = (algebraMap lam) * (1 - (algebraMap lam⁻¹) * a)

    This algebraic identity allows us to reduce invertibility of lam·1 - a
    to the Neumann series condition ‖T‖ < 1 where T = lam⁻¹·a. -/
theorem resolvent_factorization (a : A) {lam : 𝕜} (hlam : lam ≠ 0) :
    algebraMap 𝕜 A lam - a =
    algebraMap 𝕜 A lam * (1 - algebraMap 𝕜 A lam⁻¹ * a) := by
  rw [mul_sub, mul_one, ← mul_assoc]
  congr 1
  rw [← map_mul, mul_inv_cancel₀ hlam, map_one, one_mul]

/-- **Resolvent existence via Neumann series**

    For a in a Banach algebra and lam with ‖a‖ < ‖lam‖, the element
    (lam·1 - a) is invertible. This shows lam is in the resolvent set of a.

    Proof strategy: Factor lam·1 - a = lam·(1 - lam⁻¹a). Since ‖lam⁻¹a‖ < 1,
    the Neumann series shows (1 - lam⁻¹a) is a unit. Since lam ≠ 0,
    lam·1 is also a unit. The product is therefore a unit. -/
theorem resolvent_isUnit (a : A) {lam : 𝕜} (hlam : lam ≠ 0) (ha : ‖a‖ < ‖lam‖) :
    IsUnit (algebraMap 𝕜 A lam - a) := by
  rw [resolvent_factorization a hlam]
  exact IsUnit.mul (algebraMap_isUnit hlam) (one_sub_isUnit _ (norm_inv_smul_lt_one a hlam ha))

-- ══════════════════════════════════════════════════════════════════
-- § 3. Neumann Series Representation of the Resolvent
-- ══════════════════════════════════════════════════════════════════

/-- **Summability of the resolvent series**

    The series ∑ (lam⁻¹·a)^n is summable when ‖a‖ < ‖lam‖. -/
theorem resolvent_series_summable (a : A) {lam : 𝕜} (hlam : lam ≠ 0) (ha : ‖a‖ < ‖lam‖) :
    Summable (fun n : ℕ => (algebraMap 𝕜 A lam⁻¹ * a) ^ n) :=
  neumann_summable _ (norm_inv_smul_lt_one a hlam ha)

/-- **Neumann series for the resolvent**

    Ring.inverse (lam·1 - a) = (algebraMap lam⁻¹) * ∑ (lam⁻¹·a)^n

    This gives an explicit power series for the resolvent R(lam,a),
    valid whenever ‖a‖ < ‖lam‖. This is the operator-theoretic version
    of 1/(lam - x) = lam⁻¹ · ∑ (x/lam)^n for |x| < |lam|. -/
theorem resolvent_eq_neumann_series (a : A) {lam : 𝕜} (hlam : lam ≠ 0) (ha : ‖a‖ < ‖lam‖) :
    Ring.inverse (algebraMap 𝕜 A lam - a) =
    algebraMap 𝕜 A lam⁻¹ * ∑' n : ℕ, (algebraMap 𝕜 A lam⁻¹ * a) ^ n := by
  set T := algebraMap 𝕜 A lam⁻¹ * a
  have hT : ‖T‖ < 1 := norm_inv_smul_lt_one a hlam ha
  -- Ring.inverse (lam·(1 - T)) = Ring.inverse (1 - T) * Ring.inverse (lam·1)
  rw [resolvent_factorization a hlam]
  -- Ring.inverse of product of units
  have hlam_unit := algebraMap_isUnit (A := A) hlam
  have h1T_unit := one_sub_isUnit T hT
  -- Ring.inverse (lam * (1 - T)) = Ring.inverse (1 - T) * Ring.inverse (lam·1)
  rw [Ring.inverse_mul (Or.inl hlam_unit)]
  -- Ring.inverse (algebraMap lam) = algebraMap lam⁻¹
  have hu : algebraMap 𝕜 A lam * algebraMap 𝕜 A lam⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hlam, map_one]
  have hu' : algebraMap 𝕜 A lam⁻¹ * algebraMap 𝕜 A lam = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hlam, map_one]
  have hinv : Ring.inverse (algebraMap 𝕜 A lam) = algebraMap 𝕜 A lam⁻¹ :=
    Ring.inverse_unit (Units.mk (algebraMap 𝕜 A lam) (algebraMap 𝕜 A lam⁻¹) hu hu')
  rw [hinv, ← neumann_sum T hT]
  -- algebraMap lam⁻¹ is central, so it commutes with ∑ T^n
  exact (Algebra.commutes lam⁻¹ _).symm

-- ══════════════════════════════════════════════════════════════════
-- § 4. Norm Bound on the Resolvent
-- ══════════════════════════════════════════════════════════════════

/-- **Resolvent norm bound**

    ‖R(lam,a)‖ ≤ ‖lam‖⁻¹ · (1 - ‖lam‖⁻¹ · ‖a‖)⁻¹ = 1/(‖lam‖ - ‖a‖)

    This is the quantitative bound that makes the resolvent useful
    for contour integration. As |lam| → ∞, ‖R(lam,a)‖ → 0. -/
theorem resolvent_norm_bound (a : A) {lam : 𝕜} (hlam : lam ≠ 0) (ha : ‖a‖ < ‖lam‖) :
    ‖Ring.inverse (algebraMap 𝕜 A lam - a)‖ ≤ (‖lam‖ - ‖a‖)⁻¹ := by
  set T := algebraMap 𝕜 A lam⁻¹ * a
  have hT : ‖T‖ < 1 := norm_inv_smul_lt_one a hlam ha
  rw [resolvent_eq_neumann_series a hlam ha]
  calc ‖algebraMap 𝕜 A lam⁻¹ * ∑' n, T ^ n‖
    _ ≤ ‖algebraMap 𝕜 A lam⁻¹‖ * ‖∑' n, T ^ n‖ := norm_mul_le _ _
    _ ≤ ‖lam⁻¹‖ * (1 - ‖T‖)⁻¹ := by {
        rw [norm_algebraMap]
        exact mul_le_mul_of_nonneg_left (norm_neumann_le T hT) (norm_nonneg _)
      }
    _ = ‖lam‖⁻¹ * (1 - ‖T‖)⁻¹ := by rw [norm_inv]
    _ ≤ ‖lam‖⁻¹ * (1 - ‖lam‖⁻¹ * ‖a‖)⁻¹ := by {
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
        apply inv_anti₀
        · have h1 : ‖lam‖⁻¹ * ‖a‖ < ‖lam‖⁻¹ * ‖lam‖ :=
            mul_lt_mul_of_pos_left ha (inv_pos.mpr (norm_pos_iff.mpr hlam))
          have h2 : ‖lam‖⁻¹ * ‖lam‖ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr hlam)
          linarith
        · calc 1 - ‖lam‖⁻¹ * ‖a‖
            _ ≤ 1 - ‖T‖ := by {
                apply sub_le_sub_left
                calc ‖T‖ ≤ ‖algebraMap 𝕜 A lam⁻¹‖ * ‖a‖ := norm_mul_le _ _
                _ = ‖lam‖⁻¹ * ‖a‖ := by rw [norm_algebraMap, norm_inv]
              }
      }
    _ = (‖lam‖ - ‖a‖)⁻¹ := by {
        have hlam' : ‖lam‖ ≠ 0 := norm_ne_zero_iff.mpr hlam
        have hpos : (0:ℝ) < 1 - ‖lam‖⁻¹ * ‖a‖ := by
          have h1 : ‖lam‖⁻¹ * ‖a‖ < ‖lam‖⁻¹ * ‖lam‖ :=
            mul_lt_mul_of_pos_left ha (inv_pos.mpr (norm_pos_iff.mpr hlam))
          have h2 : ‖lam‖⁻¹ * ‖lam‖ = 1 := inv_mul_cancel₀ hlam'
          linarith
        have hsub : (0:ℝ) < ‖lam‖ - ‖a‖ := by linarith
        field_simp [hlam', hpos.ne', hsub.ne']
      }

-- ══════════════════════════════════════════════════════════════════
-- § 5. First Resolvent Identity (Algebraic)
-- ══════════════════════════════════════════════════════════════════

/-- **First resolvent identity**

    R(lam) - R(μ) = (μ - lam) · R(lam) · R(μ)

    This purely algebraic identity holds for any two points in the
    resolvent set. It is fundamental to spectral theory: it shows
    the resolvent is a "pseudo-resolvent" and implies analyticity.

    Proof: Multiply both sides by (lam·1-a) on the left and (μ·1-a)
    on the right, reducing to the tautology (μ-lam)·1 = (μ-lam)·1. -/
theorem first_resolvent_identity (a : A) {lam μ : 𝕜}
    (hlam : IsUnit (algebraMap 𝕜 A lam - a)) (hμ : IsUnit (algebraMap 𝕜 A μ - a)) :
    Ring.inverse (algebraMap 𝕜 A lam - a) - Ring.inverse (algebraMap 𝕜 A μ - a) =
    (algebraMap 𝕜 A μ - algebraMap 𝕜 A lam) *
    Ring.inverse (algebraMap 𝕜 A lam - a) * Ring.inverse (algebraMap 𝕜 A μ - a) := by
  -- Extract units
  obtain ⟨ulam, hulam⟩ := hlam
  obtain ⟨uμ, huμ⟩ := hμ
  -- Work with Ring.inverse as unit inverses
  have Rlam : Ring.inverse (algebraMap 𝕜 A lam - a) = ↑ulam⁻¹ := by
    rw [← hulam]; exact Ring.inverse_unit ulam
  have Rμ : Ring.inverse (algebraMap 𝕜 A μ - a) = ↑uμ⁻¹ := by
    rw [← huμ]; exact Ring.inverse_unit uμ
  rw [Rlam, Rμ]
  -- Key identity: ulam⁻¹ - uμ⁻¹ = ulam⁻¹ * (uμ - ulam) * uμ⁻¹
  -- Since ulam = lam·1 - a and uμ = μ·1 - a, we get uμ - ulam = (μ-lam)·1
  have hulamμ : (↑uμ : A) - ↑ulam = algebraMap 𝕜 A μ - algebraMap 𝕜 A lam := by
    rw [huμ, hulam]; abel
  -- The algebraic identity for unit inverses
  have key : (↑ulam⁻¹ : A) - ↑uμ⁻¹ = ↑ulam⁻¹ * (↑uμ - ↑ulam) * ↑uμ⁻¹ := by
    rw [show (↑ulam⁻¹ : A) - ↑uμ⁻¹ =
        ↑ulam⁻¹ * (↑uμ * ↑uμ⁻¹) - (↑ulam⁻¹ * ↑ulam) * ↑uμ⁻¹ from by
      simp]
    noncomm_ring
  rw [key, hulamμ]
  -- algebraMap μ - algebraMap lam is central, so it commutes with ↑ulam⁻¹
  rw [show (↑ulam⁻¹ : A) * (algebraMap 𝕜 A μ - algebraMap 𝕜 A lam) =
      (algebraMap 𝕜 A μ - algebraMap 𝕜 A lam) * (↑ulam⁻¹ : A) from by
    rw [mul_sub, sub_mul, Algebra.commutes μ, Algebra.commutes lam]]

-- ══════════════════════════════════════════════════════════════════
-- § 6. Resolvent Vanishes at Infinity
-- ══════════════════════════════════════════════════════════════════

/-- **Resolvent vanishes at infinity**

    ‖R(lam,a)‖ ≤ 1/(‖lam‖ - ‖a‖) → 0 as ‖lam‖ → ∞.

    This is essential for the holomorphic functional calculus:
    it ensures that ∮ f(lam)R(lam,a) dlam converges when the contour
    is sufficiently large and f is bounded. -/
theorem resolvent_tendsto_zero (a : A) :
    Filter.Tendsto (fun lam : 𝕜 => Ring.inverse (algebraMap 𝕜 A lam - a))
    (Filter.comap (fun lam => ‖lam‖) Filter.atTop) (nhds 0) := by
  apply squeeze_zero_norm'
  · -- Eventually ‖R(lam,a)‖ ≤ (‖lam‖ - ‖a‖)⁻¹
    rw [Filter.eventually_iff, Filter.mem_comap]
    refine ⟨{r : ℝ | ‖a‖ + 1 ≤ r}, Filter.mem_atTop _, fun lam hlam => ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hlam
    have hpos : 0 < ‖lam‖ := by linarith [norm_nonneg a]
    exact resolvent_norm_bound a (norm_pos_iff.mp hpos) (by linarith)
  · -- (‖lam‖ - ‖a‖)⁻¹ → 0 as ‖lam‖ → ∞
    have h_sub : Filter.Tendsto (fun r : ℝ => r - ‖a‖) Filter.atTop Filter.atTop := by
      intro s hs
      obtain ⟨b, hb⟩ := Filter.mem_atTop_sets.mp hs
      apply Filter.mem_atTop_sets.mpr
      exact ⟨b + ‖a‖, fun r hr => hb _ (by linarith)⟩
    exact (tendsto_inv_atTop_zero.comp h_sub).comp Filter.tendsto_comap

end ResolventNeumann
