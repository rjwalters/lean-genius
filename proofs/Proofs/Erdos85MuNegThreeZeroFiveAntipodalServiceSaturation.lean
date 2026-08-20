import Proofs.Erdos85EdgeIndexedServiceCommonStarSaturation
import Proofs.Erdos85MuNegThreeZeroFiveInternalTwoWalkMass

/-! # Antipodal h305 service-star saturation -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

set_option maxRecDepth 100000 in
theorem h305_antipodal_nonendpointEligible_mass_two :
    ∀ i j k : ZMod 8, j - i = 4 →
      k ∈ h305ServiceNonendpointEligibleCoordinates i j →
      h305InternalTwoWalkCoordinateMass i j k = 2 := by
  native_decide

/-- At either nonendpoint eligible coordinate of a central antipodal h305
edge, every exterior edge through that coordinate shares a service neighbor
with the central edge. -/
theorem h305_antipodal_incidentServiceCommon_saturates
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i j k : ZMod 8) (hij : i ≠ j)
    (ha : a.1.toFinset = {u i, u j})
    (hoffset : j - i = 4)
    (hk : k ∈ h305ServiceNonendpointEligibleCoordinates i j) :
    incidentServiceCommonEdgeValues R Cedge (u k) a =
      R.incidenceFinset (u k) := by
  apply incidentServiceCommonEdgeValues_eq_incidenceFinset_of_six
    R Cedge hRreg
  rw [h305_incidentServiceCommonEdge_card_eq_coordinate_add_four
    H R Cedge hservice hHreg hCreg hfree u huinj hu
      a i j k hij ha hk]
  rw [h305_antipodal_nonendpointEligible_mass_two i j k hoffset hk]

end

end Erdos85

#print axioms Erdos85.h305_antipodal_incidentServiceCommon_saturates
