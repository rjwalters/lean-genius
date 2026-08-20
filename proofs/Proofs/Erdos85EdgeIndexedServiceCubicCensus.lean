import Proofs.Erdos85EdgeIndexedServiceCubicEquation

/-! # Finite census form of the cubic edge-service equation -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Length-three exterior-walk mass over all edges incident to `u`. -/
def incidentServiceCubicWalkMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : V) (a : R.edgeFinset) : ℕ :=
  ∑ b : R.edgeFinset, if u ∈ b.1.toFinset then
    Fintype.card {p : Cedge.Walk b a | p.length = 3} else 0

/-- Length-three internal-walk mass from `u` to the endpoints of `a`. -/
def internalEndpointCubicWalkMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (u : V) (a : R.edgeFinset) : ℕ :=
  ∑ v : V, if v ∈ a.1.toFinset then
    Fintype.card {p : H.Walk u v | p.length = 3} else 0

theorem edgeIncidence_mul_service_cube_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : V) (a : R.edgeFinset) :
    ((edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ ^ 3 :
        Matrix V R.edgeFinset ℂ) u a) =
      (incidentServiceCubicWalkMass R Cedge u a : ℂ) := by
  classical
  rw [Matrix.mul_apply]
  simp only [incidentServiceCubicWalkMass, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Cedge.adjMatrix_pow_apply_eq_card_walk (α := ℂ) 3 b a]
  by_cases hu : u ∈ b.1.toFinset <;>
    simp [edgeEndpointIncidenceMatrix, hu]

theorem internalCube_mul_edgeIncidence_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (u : V) (a : R.edgeFinset) :
    ((H.adjMatrix ℂ ^ 3 * edgeEndpointIncidenceMatrix R :
        Matrix V R.edgeFinset ℂ) u a) =
      (internalEndpointCubicWalkMass H R u a : ℂ) := by
  classical
  rw [Matrix.mul_apply]
  simp only [internalEndpointCubicWalkMass, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [H.adjMatrix_pow_apply_eq_card_walk (α := ℂ) 3 u v]
  by_cases hv : v ∈ a.1.toFinset <;>
    simp [edgeEndpointIncidenceMatrix, hv]

/-- Exact natural-number census behind `I C³ = 28J - H³I`: the exterior
and internal endpoint-weighted cubic-walk masses partition the constant 28. -/
theorem edgeIndexedService_cubicWalkCensus
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (u : V) (a : R.edgeFinset) :
    incidentServiceCubicWalkMass R Cedge u a +
        internalEndpointCubicWalkMass H R u a = 28 := by
  have heq := congrFun (congrFun
    (edgeIndexedService_cubicEquation_two_six H R Cedge hservice hHreg hCreg)
    u) a
  rw [edgeIncidence_mul_service_cube_apply] at heq
  simp only [Matrix.sub_apply, Matrix.smul_apply, edgeIndexedOnesMatrix,
    smul_eq_mul, mul_one] at heq
  rw [internalCube_mul_edgeIncidence_apply] at heq
  have hreal := congrArg Complex.re heq
  norm_num at hreal
  have hsum :
      (incidentServiceCubicWalkMass R Cedge u a : ℝ) +
        internalEndpointCubicWalkMass H R u a = 28 := by
    linarith
  exact_mod_cast hsum

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_cubicWalkCensus
