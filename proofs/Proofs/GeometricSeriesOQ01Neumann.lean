import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-
# Neumann Series for Bounded Operators

## What This Proves
The Neumann series theorem: for a bounded linear operator T on a Banach space
with operator norm ‖T‖ < 1, the operator (I - T) is invertible and
  (I - T)⁻¹ = ∑ₙ Tⁿ

This extends the scalar geometric series ∑ rⁿ = 1/(1-r) to the operator setting.

## Historical Context
Carl Neumann (1877) introduced this series in potential theory to solve
integral equations. The result is fundamental to:
- Perturbation theory: if A is invertible and ‖A⁻¹B‖ < 1, then A + B is invertible
- Resolvent operators: (λI - T)⁻¹ = λ⁻¹ ∑ (T/λ)ⁿ for |λ| > ‖T‖
- Fixed-point theory: the contraction mapping theorem

## Approach
The proof leverages Mathlib's `geom_series_mul_neg` and `mul_neg_geom_series`
for complete normed rings. Since E →L[𝕜] E (the bounded operators) form a
normed algebra (hence a complete normed ring when E is a Banach space),
the Neumann series is an immediate consequence.
-/

namespace NeumannSeries

open ContinuousLinearMap Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The operator geometric series ∑ Tⁿ is summable when ‖T‖ < 1.
This is an instance of `NormedRing.summable_geometric_of_norm_lt_one`
applied to the normed algebra E →L[𝕜] E. -/
theorem operator_geometric_summable (T : E →L[𝕜] E) (hT : ‖T‖ < 1) :
    Summable (fun n : ℕ => T ^ n) :=
  NormedRing.summable_geometric_of_norm_lt_one T hT

/-- The Neumann series identity: (∑ Tⁿ) * (1 - T) = 1.
Here 1 is the identity operator and multiplication is composition. -/
theorem neumann_series_mul_right (T : E →L[𝕜] E) (hT : ‖T‖ < 1) :
    (∑' n : ℕ, T ^ n) * (1 - T) = 1 :=
  geom_series_mul_neg T hT

/-- Left multiplication: (1 - T) * (∑ Tⁿ) = 1. -/
theorem neumann_series_mul_left (T : E →L[𝕜] E) (hT : ‖T‖ < 1) :
    (1 - T) * (∑' n : ℕ, T ^ n) = 1 :=
  mul_neg_geom_series T hT

/-- The operator (1 - T) is a unit (invertible) when ‖T‖ < 1. -/
noncomputable def oneSub_isUnit (T : E →L[𝕜] E) (hT : ‖T‖ < 1) :
    Units (E →L[𝕜] E) where
  val := 1 - T
  inv := ∑' n : ℕ, T ^ n
  val_inv := neumann_series_mul_left T hT
  inv_val := neumann_series_mul_right T hT

/-- The inverse of (1 - T) equals ∑ Tⁿ: the Neumann series. -/
theorem oneSub_inv_eq_tsum (T : E →L[𝕜] E) (hT : ‖T‖ < 1) :
    ↑(oneSub_isUnit T hT)⁻¹ = ∑' n : ℕ, T ^ n := rfl

/-- (1 - T) is invertible as a ring element. -/
theorem isUnit_oneSub (T : E →L[𝕜] E) (hT : ‖T‖ < 1) :
    IsUnit (1 - T : E →L[𝕜] E) :=
  ⟨oneSub_isUnit T hT, rfl⟩

/-- Operator norm bound: ‖∑ Tⁿ‖ ≤ ‖1‖ - 1 + 1/(1 - ‖T‖).
This uses the general normed ring bound from Mathlib. -/
theorem neumann_series_norm_bound (T : E →L[𝕜] E) (hT : ‖T‖ < 1) :
    ‖∑' n : ℕ, T ^ n‖ ≤ ‖(1 : E →L[𝕜] E)‖ - 1 + (1 - ‖T‖)⁻¹ :=
  NormedRing.tsum_geometric_of_norm_lt_one T hT

/-- The first few terms of the Neumann series: partial sum formula.
This is `geom_sum_mul_neg` from Mathlib applied to the operator ring. -/
theorem neumann_partial_sum (T : E →L[𝕜] E) (n : ℕ) :
    (∑ k ∈ Finset.range n, T ^ k) * (1 - T) = 1 - T ^ n :=
  geom_sum_mul_neg T n

/-- Convergence: the partial sums of the Neumann series converge to (1 - T)⁻¹
in operator norm when ‖T‖ < 1. -/
theorem neumann_partial_sum_tendsto (T : E →L[𝕜] E) (hT : ‖T‖ < 1) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, T ^ k) atTop
      (nhds (∑' n : ℕ, T ^ n)) :=
  (operator_geometric_summable T hT).hasSum.tendsto_sum_nat

end NeumannSeries
