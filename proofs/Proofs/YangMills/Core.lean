import Mathlib

/-
# Yang-Mills Core: Gauge Groups, Lie Algebras, and Spacetime

Epistemic status: RIGOROUS — definitions and proven theorems only.
No axioms, no physics assumptions. Everything here is provable from Mathlib.

This module provides the mathematical foundation for Yang-Mills theory:
- CompactSimpleGaugeGroup: typeclass for compact simple Lie groups (SU(2), SU(3))
- GaugeLieAlgebra: Lie algebra with bracket, anticommutativity, Jacobi identity
- Spacetime: ℝ⁴ with Minkowski metric η_μν = diag(-1,+1,+1,+1)

All Minkowski metric properties are fully proven:
symmetry, diagonality, signature (1,3), trace = 2, norm squared.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped Topology BigOperators Matrix

namespace YangMillsMassGap

/-- A compact simple gauge group. Examples: SU(2), SU(3).
    For the Millennium Problem, G must be compact and simple (non-abelian). -/
class CompactSimpleGaugeGroup (G : Type*) extends Group G, TopologicalSpace G where
  compact : CompactSpace G
  connected : ConnectedSpace G
  simple : ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤

/-- The Lie algebra 𝔤 associated to a gauge group G.
    For SU(n), this is the space of traceless anti-Hermitian n×n matrices. -/
structure GaugeLieAlgebra (G : Type*) [CompactSimpleGaugeGroup G] where
  carrier : Type*
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℝ carrier]
  bracket : carrier → carrier → carrier
  bracket_anticomm : ∀ x y, bracket x y = - bracket y x
  bracket_jacobi : ∀ x y z, bracket x (bracket y z) + bracket y (bracket z x) +
                           bracket z (bracket x y) = 0

attribute [instance] GaugeLieAlgebra.addCommGroup GaugeLieAlgebra.module

/-- Spacetime ℝ⁴ -/
abbrev Spacetime := Fin 4 → ℝ

/-- Minkowski metric signature (−,+,+,+) -/
def minkowskiSignature (μ : Fin 4) : ℝ :=
  if μ = 0 then -1 else 1

/-- Minkowski metric η_μν -/
def minkowskiMetric (μ ν : Fin 4) : ℝ :=
  if μ = ν then minkowskiSignature μ else 0

theorem minkowski_symmetric (μ ν : Fin 4) : minkowskiMetric μ ν = minkowskiMetric ν μ := by
  unfold minkowskiMetric
  by_cases h : μ = ν
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The Minkowski metric is diagonal. -/
theorem minkowski_diagonal (μ ν : Fin 4) (h : μ ≠ ν) :
    minkowskiMetric μ ν = 0 := by
  simp [minkowskiMetric, h]

/-- The time-time component η₀₀ = -1. -/
theorem minkowski_time_component : minkowskiMetric 0 0 = -1 := by
  simp [minkowskiMetric, minkowskiSignature]

/-- The space-space components η_ii = 1 for i ≥ 1. -/
theorem minkowski_space_component (i : Fin 4) (hi : i ≠ 0) :
    minkowskiMetric i i = 1 := by
  simp [minkowskiMetric, minkowskiSignature, hi]

/-- The trace η^μ_μ = -1 + 1 + 1 + 1 = 2. -/
theorem minkowski_trace :
    (Finset.univ : Finset (Fin 4)).sum (fun μ => minkowskiMetric μ μ) = 2 := by
  simp [minkowskiMetric, minkowskiSignature, Fin.sum_univ_four]
  norm_num

/-- The Minkowski metric has Lorentzian signature (1, 3):
    exactly one negative diagonal entry and three positive ones. -/
theorem minkowski_signature_count :
    ((Finset.univ : Finset (Fin 4)).filter (fun μ => minkowskiSignature μ < 0)).card = 1 ∧
    ((Finset.univ : Finset (Fin 4)).filter (fun μ => minkowskiSignature μ > 0)).card = 3 := by
  -- native_decide fails here because Real.decidableLT has no executable code in
  -- noncomputable section. We prove it by case analysis instead.
  constructor
  · -- Count negative entries: only μ = 0 gives minkowskiSignature μ = -1 < 0
    have : (Finset.univ : Finset (Fin 4)).filter (fun μ => minkowskiSignature μ < 0) = {0} := by
      ext μ; simp [minkowskiSignature]; fin_cases μ <;> simp <;> norm_num
    rw [this]; simp
  · -- Count positive entries: μ = 1, 2, 3 give minkowskiSignature μ = 1 > 0
    have : (Finset.univ : Finset (Fin 4)).filter (fun μ => minkowskiSignature μ > 0) = {1, 2, 3} := by
      ext μ; simp [minkowskiSignature]; fin_cases μ <;> simp <;> norm_num
    rw [this]; simp

/-- The squared Minkowski norm of a spacetime vector:
    ‖x‖² = -x₀² + x₁² + x₂² + x₃². -/
def minkowskiNormSq (x : Spacetime) : ℝ :=
  (Finset.univ : Finset (Fin 4)).sum (fun μ =>
    (Finset.univ : Finset (Fin 4)).sum (fun ν =>
      minkowskiMetric μ ν * x μ * x ν))

/-- The Minkowski norm squared simplifies to diagonal terms since η is diagonal. -/
theorem minkowskiNormSq_eq (x : Spacetime) :
    minkowskiNormSq x = (Finset.univ : Finset (Fin 4)).sum
      (fun μ => minkowskiMetric μ μ * x μ * x μ) := by
  unfold minkowskiNormSq
  congr 1
  ext μ
  fin_cases μ <;> simp [minkowskiMetric, minkowskiSignature, Fin.sum_univ_four] <;> ring

end YangMillsMassGap
