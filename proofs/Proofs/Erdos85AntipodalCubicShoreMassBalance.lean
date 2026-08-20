import Proofs.Erdos85AntipodalCubicEndpointBudget
import Proofs.Erdos85EdgeIndexedServiceCubicTypeMass

/-! # Antipodal h305 cubic shore-mass balance -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 100000 in
theorem h305_antipodal_cubicCoordinateBudget_sum :
    ∀ i : ZMod 8, (∑ j : ZMod 8,
      if j = i + 1 ∨ j = i + 3 ∨ j = i + 5 ∨ j = i + 7 then 24 else 28) =
      208 := by
  native_decide

/-- Across the eight vertices of the shore containing an antipodal target
edge, the incident service cubic mass is exactly `4·24 + 4·28 = 208`. -/
theorem h305_antipodal_incidentServiceCubicWalkMass_shore_sum_eq_208
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i : ZMod 8)
    (ha : a.1.toFinset = {u i, u (i + 4)}) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    (∑ x ∈ U, incidentServiceCubicWalkMass R Cedge x a) = 208 := by
  classical
  dsimp only
  rw [Finset.sum_image]
  · simp_rw [incidentServiceCubicWalkMass_antipodal H R Cedge hservice
      hHreg hCreg u huinj hu a i _ ha]
    exact h305_antipodal_cubicCoordinateBudget_sum i
  · intro x _ y _ hxy
    exact huinj hxy

/-- If the complementary C8 shore contributes its forced `224` cubic mass,
then an antipodal target has type-zero cubic mass exactly eight larger than
its type-two cubic mass.  This is the graph-facing specialization of the
abstract shore/complement cancellation identity. -/
theorem h305_antipodal_shoreTypeCubicWalkMass_zero_eq_two_add_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i : ZMod 8)
    (ha : a.1.toFinset = {u i, u (i + 4)})
    (hcomplement :
      let U := (Finset.univ : Finset (ZMod 8)).image u
      (∑ x ∈ Uᶜ, incidentServiceCubicWalkMass R Cedge x a) = 224) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    shoreTypeCubicWalkMass R Cedge U 0 a =
      shoreTypeCubicWalkMass R Cedge U 2 a + 8 := by
  classical
  dsimp only at hcomplement ⊢
  let U := (Finset.univ : Finset (ZMod 8)).image u
  change (∑ x ∈ Uᶜ, incidentServiceCubicWalkMass R Cedge x a) = 224 at hcomplement
  change shoreTypeCubicWalkMass R Cedge U 0 a =
    shoreTypeCubicWalkMass R Cedge U 2 a + 8
  have hshore :
      (∑ x ∈ U, incidentServiceCubicWalkMass R Cedge x a) = 208 :=
    h305_antipodal_incidentServiceCubicWalkMass_shore_sum_eq_208
      H R Cedge hservice hHreg hCreg u huinj hu a i ha
  have hbalance := shoreTypeCubicWalkMass_balance_of_complement_sums
    R Cedge U a 208 224 hshore hcomplement
  omega

end

end Erdos85

#print axioms Erdos85.h305_antipodal_cubicCoordinateBudget_sum
#print axioms
  Erdos85.h305_antipodal_incidentServiceCubicWalkMass_shore_sum_eq_208
#print axioms
  Erdos85.h305_antipodal_shoreTypeCubicWalkMass_zero_eq_two_add_eight
