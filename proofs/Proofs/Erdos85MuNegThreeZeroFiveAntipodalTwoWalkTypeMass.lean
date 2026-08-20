import Proofs.Erdos85EdgeIndexedServiceTwoWalkTypeMass
import Proofs.Erdos85MuNegThreeZeroFiveInternalTwoWalkMass

/-! # Antipodal h305 shore-weighted two-walk mass -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 100000 in
theorem h305_antipodal_internalTwoWalkCoordinateMass_sum :
    ∀ i j : ZMod 8, j - i = 4 →
      (∑ k : ZMod 8, h305InternalTwoWalkCoordinateMass i j k) = 8 := by
  native_decide

set_option maxRecDepth 100000 in
theorem h305_antipodal_coordinates_ne :
    ∀ i j : ZMod 8, j - i = 4 → i ≠ j := by
  native_decide

/-- Across the eight vertices of the central edge's shore, an antipodal
central edge has total incident service two-walk mass `8 + 8·4 = 40`. -/
theorem h305_antipodal_incidentServiceTwoWalkMass_shore_sum_eq_forty
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i j : ZMod 8)
    (hoffset : j - i = 4)
    (ha : a.1.toFinset = {u i, u j}) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    (∑ x ∈ U, incidentServiceTwoWalkMass R Cedge x a) = 40 := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  change (∑ x ∈ U, incidentServiceTwoWalkMass R Cedge x a) = 40
  dsimp only [U]
  rw [Finset.sum_image]
  · simp_rw [h305_incidentServiceTwoWalkMass_eq_coordinate_add_four
      H R Cedge hservice hHreg hCreg u huinj hu a i j _
        (h305_antipodal_coordinates_ne i j hoffset) ha]
    rw [Finset.sum_add_distrib,
      h305_antipodal_internalTwoWalkCoordinateMass_sum i j hoffset]
    norm_num
  · intro x _ y _ hxy
    exact huinj hxy

/-- Endpoint-weighted common-service-neighbor form of the same exact mass. -/
theorem h305_antipodal_endpointWeighted_common_sum_eq_forty
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i j : ZMod 8)
    (hoffset : j - i = 4)
    (ha : a.1.toFinset = {u i, u j}) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    (∑ b : R.edgeFinset,
      (Cedge.neighborFinset b ∩ Cedge.neighborFinset a).card *
        (b.1.toFinset ∩ U).card) = 40 := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  rw [← sum_incidentServiceTwoWalkMass_eq_endpointWeighted_common
    R Cedge U a]
  exact h305_antipodal_incidentServiceTwoWalkMass_shore_sum_eq_forty
    H R Cedge hservice hHreg hCreg u huinj hu a i j hoffset ha

end

end Erdos85

#print axioms
  Erdos85.h305_antipodal_endpointWeighted_common_sum_eq_forty
