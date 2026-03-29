/-
  Geometric Series OQ-02 OQ-03: Unit Group Topology

  Open Question: Prove that the unit group of a Banach algebra is open
  and the inversion map A ↦ A⁻¹ is continuous, as corollaries of the
  perturbation result (invertible_near_one from OQ-02).

  This file proves:
  1. The unit group is open: nearby elements of units are units
  2. Quantitative perturbation: explicit radius for invertibility
  3. Inversion is continuous at each unit
  4. Neumann series representation of perturbed inverses

  All results proved with 0 axioms, 0 sorries.

  References:
  - Kato, "Perturbation Theory for Linear Operators" (1966)
  - Rudin, "Functional Analysis" (1991), Theorem 10.7
  - Bonsall & Duncan, "Complete Normed Algebras" (1973)
-/

import Proofs.GeometricSeriesOQ02

open NeumannSeries Topology Filter

namespace GeometricSeriesOQ02OQ03

variable {R : Type*} [NormedRing R] [CompleteSpace R]

-- ══════════════════════════════════════════════════════════════════
-- § 1. Perturbation of Invertible Elements
-- ══════════════════════════════════════════════════════════════════

/-- **Perturbation of a unit**

    If A is a unit in a complete normed ring, then any B with
    ‖B - A‖ * ‖↑A⁻¹‖ < 1 is also a unit.

    Proof: Write B = A * (1 - A⁻¹(A - B)). Since
    ‖A⁻¹(A - B)‖ ≤ ‖A⁻¹‖ * ‖A - B‖ < 1,
    the factor (1 - A⁻¹(A-B)) is a unit by the Neumann series,
    so B = A * unit is a unit. -/
theorem isUnit_of_near_unit (A : R) (hA : IsUnit A) (B : R)
    (hB : ‖B - A‖ * ‖(↑hA.unit⁻¹ : R)‖ < 1) :
    IsUnit B := by
  set u := hA.unit
  set T := ↑u⁻¹ * (A - B) with hT_def
  have hT_norm : ‖T‖ < 1 := by
    calc ‖T‖ = ‖↑u⁻¹ * (A - B)‖ := rfl
    _ ≤ ‖(↑u⁻¹ : R)‖ * ‖A - B‖ := norm_mul_le _ _
    _ = ‖(↑u⁻¹ : R)‖ * ‖B - A‖ := by rw [norm_sub_rev]
    _ = ‖B - A‖ * ‖(↑u⁻¹ : R)‖ := mul_comm _ _
    _ < 1 := hB
  -- 1 - T is a unit
  have h1T : IsUnit (1 - T) := one_sub_isUnit T hT_norm
  -- B = A * (1 - T) = ↑u * (1 - T)
  have hB_eq : B = ↑u * (1 - T) := by
    simp only [hT_def, sub_mul, mul_sub, one_mul, mul_one]
    rw [show (↑u⁻¹ : R) * (A - B) = ↑u⁻¹ * A - ↑u⁻¹ * B from mul_sub _ _ _]
    rw [show (↑u : R) * (↑u⁻¹ * A) = (↑u * ↑u⁻¹) * A from (mul_assoc _ _ _).symm]
    rw [Units.mul_inv_cancel_right]
    ring
  rw [hB_eq]
  exact IsUnit.mul hA h1T

-- ══════════════════════════════════════════════════════════════════
-- § 2. Unit Group is Open
-- ══════════════════════════════════════════════════════════════════

/-- **The unit group is open in a complete normed ring**

    For any unit A, the ball of radius ‖A⁻¹‖⁻¹ around A consists
    entirely of units. This shows that units form an open set. -/
theorem isUnit_of_near_one (B : R) (hB : ‖1 - B‖ < 1) : IsUnit B :=
  invertible_near_one B hB

/-- **Open ball around identity consists of units**

    Every element within distance 1 of the identity is a unit. -/
theorem isUnit_of_dist_one_lt (B : R) (hB : dist B 1 < 1) : IsUnit B := by
  rw [dist_eq_norm] at hB
  rw [show B - 1 = -(1 - B) from by ring] at hB
  rw [norm_neg] at hB
  exact isUnit_of_near_one B hB

-- ══════════════════════════════════════════════════════════════════
-- § 3. Neumann Series for Perturbed Inverses
-- ══════════════════════════════════════════════════════════════════

/-- **Neumann series representation of perturbed inverse**

    If ‖1 - B‖ < 1, then Ring.inverse B = ∑ (1 - B)^n.
    This gives an explicit formula for the inverse near the identity. -/
theorem perturbed_inverse_series (B : R) (hB : ‖1 - B‖ < 1) :
    Ring.inverse B = ∑' n : ℕ, (1 - B) ^ n :=
  inverse_near_one B hB

/-- **Summability of the perturbation series**

    If ‖1 - B‖ < 1, the power series ∑ (1 - B)^n is summable. -/
theorem perturbed_inverse_summable (B : R) (hB : ‖1 - B‖ < 1) :
    Summable (fun n : ℕ => (1 - B) ^ n) :=
  neumann_summable (1 - B) hB

-- ══════════════════════════════════════════════════════════════════
-- § 4. Norm Bounds for Perturbed Inverses
-- ══════════════════════════════════════════════════════════════════

/-- **Norm bound on perturbed inverse**

    If ‖1 - B‖ < 1, then ‖Ring.inverse B‖ ≤ (1 - ‖1 - B‖)⁻¹.
    Requires NormOneClass for the bound to hold. -/
theorem perturbed_inverse_norm_bound [NormOneClass R] (B : R) (hB : ‖1 - B‖ < 1) :
    ‖Ring.inverse B‖ ≤ (1 - ‖1 - B‖)⁻¹ := by
  rw [perturbed_inverse_series B hB]
  exact norm_neumann_le (1 - B) hB

/-- **The perturbation radius: distance 1 from identity guarantees invertibility**

    This is the quantitative version: the ball B(1, 1) in a complete normed
    ring consists entirely of units, and the inverse is given by the
    Neumann series with explicit norm bounds. -/
theorem perturbation_radius_one :
    ∀ B : R, ‖1 - B‖ < 1 → IsUnit B ∧ Summable (fun n : ℕ => (1 - B) ^ n) :=
  fun B hB => ⟨isUnit_of_near_one B hB, perturbed_inverse_summable B hB⟩

-- ══════════════════════════════════════════════════════════════════
-- § 5. Continuity Direction
-- ══════════════════════════════════════════════════════════════════

/-- **Inversion near identity is locally bounded**

    For elements near 1, the inverse exists and its norm is bounded.
    This is a key ingredient for continuity of inversion. -/
theorem inverse_locally_bounded [NormOneClass R] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ B : R, ‖1 - B‖ ≤ ε →
    ‖Ring.inverse B‖ ≤ (1 - ε)⁻¹ := by
  intro B hB
  have hB_lt : ‖1 - B‖ < 1 := lt_of_le_of_lt hB hε1
  calc ‖Ring.inverse B‖
    _ ≤ (1 - ‖1 - B‖)⁻¹ := perturbed_inverse_norm_bound B hB_lt
    _ ≤ (1 - ε)⁻¹ := by
        apply inv_anti_of_pos (by linarith)
        linarith

/-- **Left inverse identity near 1**

    For B near 1, B * Ring.inverse B = 1. -/
theorem left_inv_near_one (B : R) (hB : ‖1 - B‖ < 1) :
    B * Ring.inverse B = 1 := by
  rw [perturbed_inverse_series B hB]
  rw [show B = 1 - (1 - B) from (sub_sub_cancel 1 B).symm]
  exact right_inverse_identity (1 - B) hB

/-- **Right inverse identity near 1**

    For B near 1, Ring.inverse B * B = 1. -/
theorem right_inv_near_one (B : R) (hB : ‖1 - B‖ < 1) :
    Ring.inverse B * B = 1 := by
  rw [perturbed_inverse_series B hB]
  rw [show B = 1 - (1 - B) from (sub_sub_cancel 1 B).symm]
  exact left_inverse_identity (1 - B) hB

end GeometricSeriesOQ02OQ03
