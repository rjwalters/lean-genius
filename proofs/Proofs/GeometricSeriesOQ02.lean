import Mathlib.Algebra.Group.NatPowAssoc
import Mathlib.Algebra.Ring.Regular
import Mathlib.Tactic.Abel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-
# Geometric Series for Matrices and Operators (Neumann Series)

## What This Proves
The Neumann series: for an element T in a complete normed ring with ‖T‖ < 1,
the geometric series ∑ T^n converges to (1 - T)⁻¹.

This generalizes the scalar geometric series formula to:
- Matrices (with operator norm)
- Bounded linear operators on Banach spaces
- Any complete normed ring

## Key Results
1. Summability: ‖T‖ < 1 implies ∑ T^n converges (in any complete normed ring)
2. Invertibility: ‖T‖ < 1 implies (1 - T) is a unit
3. Neumann series identity: ∑ T^n = Ring.inverse (1 - T)
4. Left/right inverse identities
5. Norm bound: ‖∑ T^n‖ ≤ (1 - ‖T‖)⁻¹ (with NormOneClass)
6. Finite partial sum identities
7. Perturbation of identity
8. Commutativity with generator

## Historical Note
The Neumann series is named after Carl Neumann (1832-1925), who used it
to solve integral equations. It is the operator-theoretic analogue of the
scalar geometric series and is fundamental in functional analysis, numerical
linear algebra (iterative methods), and the theory of Fredholm operators.

## Mathlib Dependencies
- `summable_geometric_of_norm_lt_one` : Series summable (NormedRing + CompleteSpace)
- `Units.oneSub` : Unit structure for (1 - T)
- `Ring.inverse_unit` : Ring.inverse ↑u = ↑u⁻¹
- `Ring.mul_inverse_cancel` / `Ring.inverse_mul_cancel` : inverse identities
-/

noncomputable section

open Finset BigOperators Topology

namespace NeumannSeries

/-
## Part 1: Convergence and Summability
-/

/-- **Neumann Series Summability**

For T in a complete normed ring with ‖T‖ < 1, the power series ∑ T^n
is summable. This is the operator-theoretic generalization of the
convergence condition |r| < 1 for scalar geometric series. -/
theorem neumann_summable {R : Type*} [NormedRing R] [CompleteSpace R]
    (T : R) (hT : ‖T‖ < 1) :
    Summable (fun n : ℕ => T ^ n) :=
  summable_geometric_of_norm_lt_one hT

/-
## Part 2: Invertibility
-/

/-- **Invertibility from Neumann Series**

If ‖T‖ < 1 in a complete normed ring, then (1 - T) is a unit (invertible).
This is the operator-theoretic version of "1 - r ≠ 0 when |r| < 1". -/
theorem one_sub_isUnit {R : Type*} [NormedRing R] [CompleteSpace R]
    (T : R) (hT : ‖T‖ < 1) :
    IsUnit (1 - T) :=
  ⟨Units.oneSub T hT, (Units.val_oneSub T hT).symm⟩

/-
## Part 3: The Sum Formula

We prove ∑ T^n = Ring.inverse (1 - T) using Units.oneSub.
The key is that Units.oneSub defines the inverse as ∑' T^n by construction.
-/

/-- **Neumann Series Sum Formula**

For T in a complete normed ring with ‖T‖ < 1:
  ∑ T^n = Ring.inverse (1 - T)

This is the fundamental identity connecting the power series to the resolvent. -/
theorem neumann_sum {R : Type*} [NormedRing R] [CompleteSpace R]
    (T : R) (hT : ‖T‖ < 1) :
    ∑' n : ℕ, T ^ n = Ring.inverse (1 - T) := by
  -- Ring.inverse (1 - T) = ↑(Units.oneSub T hT)⁻¹
  have hinv : Ring.inverse (1 - T) = ↑(Units.oneSub T hT)⁻¹ := by
    rw [← Units.val_oneSub T hT]
    exact Ring.inverse_unit (Units.oneSub T hT)
  rw [hinv]
  -- ↑(Units.oneSub T hT)⁻¹ = ∑' T^n by definition of Units.oneSub
  symm
  simp [Units.oneSub]

/-
## Part 4: Finite Partial Sums
-/

/-- **Finite geometric sum identity in rings**

For any ring element T: (1 - T) * ∑ T^k = 1 - T^n -/
theorem finite_neumann_identity {R : Type*} [Ring R] (T : R) (n : ℕ) :
    (1 - T) * ∑ k ∈ Finset.range n, T ^ k = 1 - T ^ n :=
  mul_neg_geom_sum T n

/-- **Right-multiply form of finite identity**

∑ T^k * (1 - T) = 1 - T^n -/
theorem finite_neumann_identity' {R : Type*} [Ring R] (T : R) (n : ℕ) :
    (∑ k ∈ Finset.range n, T ^ k) * (1 - T) = 1 - T ^ n :=
  geom_sum_mul_neg T n

/-
## Part 5: Left and Right Inverses
-/

/-- **Left inverse identity**

(1 - T) * ∑ T^n = 1, showing (1-T) times the Neumann series is the identity. -/
theorem left_inverse_identity {R : Type*} [NormedRing R] [CompleteSpace R]
    (T : R) (hT : ‖T‖ < 1) :
    (1 - T) * ∑' n : ℕ, T ^ n = 1 := by
  rw [neumann_sum T hT]
  exact Ring.mul_inverse_cancel _ (one_sub_isUnit T hT)

/-- **Right inverse identity**

(∑ T^n) * (1 - T) = 1, showing the Neumann series times (1-T) is the identity. -/
theorem right_inverse_identity {R : Type*} [NormedRing R] [CompleteSpace R]
    (T : R) (hT : ‖T‖ < 1) :
    (∑' n : ℕ, T ^ n) * (1 - T) = 1 := by
  rw [neumann_sum T hT]
  exact Ring.inverse_mul_cancel _ (one_sub_isUnit T hT)

/-
## Part 6: Norm Bounds
-/

/-- **Norm bound on individual terms** (for positive exponents)

Each term T^n is bounded by ‖T‖^n for n ≥ 1. -/
theorem norm_pow_le_pow_norm {R : Type*} [SeminormedRing R]
    (T : R) {n : ℕ} (hn : 0 < n) :
    ‖T ^ n‖ ≤ ‖T‖ ^ n :=
  norm_pow_le' T hn

/-- **Norm bound on the Neumann series sum**

For ‖T‖ < 1: ‖∑ T^n‖ ≤ (1 - ‖T‖)⁻¹

This follows from the triangle inequality and the scalar geometric series.
Requires NormOneClass to ensure ‖1‖ = 1 (needed for the n=0 term). -/
theorem norm_neumann_le {R : Type*} [NormedRing R] [CompleteSpace R]
    [NormOneClass R] (T : R) (hT : ‖T‖ < 1) :
    ‖∑' n : ℕ, T ^ n‖ ≤ (1 - ‖T‖)⁻¹ := by
  apply tsum_of_norm_bounded (hasSum_geometric_of_lt_one (norm_nonneg T) hT)
  exact fun n => norm_pow_le T n

/-
## Part 7: Partial Sums Convergence
-/

/-- **Partial sums converge to the Neumann series**

The finite partial sums ∑ T^k converge to Ring.inverse (1 - T). -/
theorem partial_sums_tendsto {R : Type*} [NormedRing R] [CompleteSpace R]
    (T : R) (hT : ‖T‖ < 1) :
    Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, T ^ k)
      Filter.atTop (nhds (Ring.inverse (1 - T))) := by
  rw [← neumann_sum T hT]
  exact HasSum.tendsto_sum_nat (neumann_summable T hT).hasSum

/-
## Part 8: Perturbation of Identity
-/

/-- **Perturbation of identity**

If A = 1 - T with ‖T‖ < 1, then A is invertible.
Equivalently: any element within distance 1 of the identity is a unit.
This is the foundation of perturbation theory in functional analysis. -/
theorem invertible_near_one {R : Type*} [NormedRing R] [CompleteSpace R]
    (A : R) (hA : ‖1 - A‖ < 1) :
    IsUnit A := by
  rw [show A = 1 - (1 - A) from (sub_sub_cancel 1 A).symm]
  exact one_sub_isUnit (1 - A) hA

/-- **Inverse of a perturbation of identity**

If ‖1 - A‖ < 1, then Ring.inverse A = ∑ (1-A)^n. -/
theorem inverse_near_one {R : Type*} [NormedRing R] [CompleteSpace R]
    (A : R) (hA : ‖1 - A‖ < 1) :
    Ring.inverse A = ∑' n : ℕ, (1 - A) ^ n := by
  conv_lhs => rw [show A = 1 - (1 - A) from (sub_sub_cancel 1 A).symm]
  exact (neumann_sum (1 - A) hA).symm

/-
## Part 9: Commutativity
-/

/-- **Neumann series commutes with its generator**

T commutes with ∑ T^n. This follows from the left and right inverse
identities: both show that T * S and S * T equal S - 1, where S = ∑ T^n. -/
theorem neumann_sum_comm {R : Type*} [NormedRing R] [CompleteSpace R]
    (T : R) (hT : ‖T‖ < 1) :
    T * ∑' n : ℕ, T ^ n = (∑' n : ℕ, T ^ n) * T := by
  set S := ∑' n : ℕ, T ^ n
  have hleft : (1 - T) * S = 1 := left_inverse_identity T hT
  have hright : S * (1 - T) = 1 := right_inverse_identity T hT
  -- From left: 1*S - T*S = 1, i.e., S - T*S = 1
  rw [sub_mul, one_mul] at hleft
  -- From right: S*1 - S*T = 1, i.e., S - S*T = 1
  rw [mul_sub, mul_one] at hright
  -- hleft : S - T * S = 1
  -- hright : S - S * T = 1
  -- Therefore S - T*S = S - S*T, so T*S = S*T
  have h : T * S = S * T := by
    have heq : S - T * S = S - S * T := by rw [hleft, hright]
    calc T * S = S - (S - T * S) := by abel
      _ = S - (S - S * T) := by rw [heq]
      _ = S * T := by abel
  exact h

-- The generic normed ring theorems above apply directly to matrices
-- (Matrix (Fin n) (Fin n) ℝ), bounded linear operators (E →L[𝕜] E), and
-- any other complete normed ring. Matrices inherit NormedRing and
-- CompleteSpace instances from Mathlib, so all results apply immediately.

end NeumannSeries
