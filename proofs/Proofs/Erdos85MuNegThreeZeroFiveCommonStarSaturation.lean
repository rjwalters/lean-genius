import Proofs.Erdos85MuNegThreeZeroFiveAntipodalServiceSaturation

/-! # Antipodal h305 common-star saturation -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- At either nonendpoint eligible coordinate of an antipodal h305 exterior
edge, all six exterior edges through the coordinate share a service neighbor
with the central edge. -/
theorem h305_antipodal_commonStar_saturates
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
    (a : R.edgeFinset) (i j k : ZMod 8)
    (haoffset : j - i = 4)
    (ha : a.1.toFinset = {u i, u j})
    (hk : k ∈ h305ServiceNonendpointEligibleCoordinates i j) :
    incidentServiceCommonEdgeValues R Cedge (u k) a =
      R.incidenceFinset (u k) := by
  have hij : i ≠ j := by
    intro h
    subst j
    apply (by decide : (0 : ZMod 8) ≠ 4)
    simpa using haoffset
  exact h305_antipodal_incidentServiceCommon_saturates
    H R Cedge hservice hHreg hRreg hCreg hfree u huinj hu
      a i j k hij ha haoffset hk

end

end Erdos85

#print axioms Erdos85.h305_antipodal_commonStar_saturates
