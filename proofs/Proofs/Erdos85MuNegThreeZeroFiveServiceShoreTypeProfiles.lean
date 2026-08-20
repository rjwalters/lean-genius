import Proofs.Erdos85EdgeIndexedServiceShoreTypeCounts
import Proofs.Erdos85MuNegThreeZeroFiveServiceShoreMass

/-! # The three remaining h305 service-star shore profiles -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Before using two-walk or `C₄` constraints, a same-shore h305 service star
has only three possible `(same-shore, cross-shore, opposite-shore)` neighbor
edge profiles: `(0,4,2)`, `(1,2,3)`, or `(2,0,4)`. -/
theorem h305_serviceNeighbor_shoreType_profiles
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, u j})
    (hoffset : j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
      j - i = 5 ∨ j - i = 7) :
    let U := Finset.univ.image u
    let x := serviceNeighborShoreTypeCount R Cedge a U 2
    let y := serviceNeighborShoreTypeCount R Cedge a U 1
    let z := serviceNeighborShoreTypeCount R Cedge a U 0
    (x = 0 ∧ y = 4 ∧ z = 2) ∨
      (x = 1 ∧ y = 2 ∧ z = 3) ∨
      (x = 2 ∧ y = 0 ∧ z = 4) := by
  classical
  dsimp only
  let U : Finset V := Finset.univ.image u
  let x := serviceNeighborShoreTypeCount R Cedge a U 2
  let y := serviceNeighborShoreTypeCount R Cedge a U 1
  let z := serviceNeighborShoreTypeCount R Cedge a U 0
  have hm := (h305_serviceNeighbor_shore_masses H R Cedge hservice u v
    huinj hvinj hu hdisj hcover a i j ha hoffset).1
  have hcoverMass := edgeIndexedService_sum_neighbor_endpoint_inter_card
    H R Cedge hservice a U
  have htypes := edgeIndexedService_shoreMass_eq_typeCounts
    H R Cedge hservice a U
  have htotal := edgeIndexedService_shoreTypeCounts_sum R Cedge a U
  have hdegree : (Cedge.neighborFinset a).card = 6 := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hCreg a
  change (x = 0 ∧ y = 4 ∧ z = 2) ∨
    (x = 1 ∧ y = 2 ∧ z = 3) ∨
    (x = 2 ∧ y = 0 ∧ z = 4)
  change (∑ b ∈ Cedge.neighborFinset a,
    (b.1.toFinset ∩ U).card) = 4 at hm
  change (∑ b ∈ Cedge.neighborFinset a,
    (b.1.toFinset ∩ U).card) =
      (serviceNeighborEndpointCover R Cedge a ∩ U).card at hcoverMass
  change (serviceNeighborEndpointCover R Cedge a ∩ U).card =
    2 * x + y at htypes
  change (Cedge.neighborFinset a).card = z + y + x at htotal
  omega

end

end Erdos85

#print axioms Erdos85.h305_serviceNeighbor_shoreType_profiles
