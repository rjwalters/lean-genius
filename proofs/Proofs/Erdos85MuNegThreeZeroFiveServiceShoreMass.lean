import Proofs.Erdos85EdgeIndexedServiceShoreMass
import Proofs.Erdos85MuNegThreeZeroFiveServiceEndpointCover

/-! # The 4+8 shore masses in an h305 service star -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The six neighbors of a same-shore h305 exterior edge have total endpoint
multiplicity four on its own shore and eight on the opposite shore.  Since the
neighbors are a matching, these are actual covered-vertex counts. -/
theorem h305_serviceNeighbor_shore_masses
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, u j})
    (hoffset : j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
      j - i = 5 ∨ j - i = 7) :
    (∑ b ∈ Cedge.neighborFinset a,
        (b.1.toFinset ∩ (Finset.univ.image u)).card = 4) ∧
      (∑ b ∈ Cedge.neighborFinset a,
        (b.1.toFinset ∩ (Finset.univ.image v)).card = 8) := by
  classical
  let U : Finset V := Finset.univ.image u
  let W : Finset V := Finset.univ.image v
  let E : Finset V := (h305ServiceEligibleCoordinates i j).image u
  have hd : Disjoint U W := by
    rw [Finset.disjoint_left]
    intro x hxU hxW
    rcases Finset.mem_image.mp hxU with ⟨k, -, hk⟩
    rcases Finset.mem_image.mp hxW with ⟨l, -, hl⟩
    exact hdisj k l (hk.trans hl.symm)
  have hEU : E ⊆ U := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  have hcoverEq : serviceNeighborEndpointCover R Cedge a = E ∪ W := by
    simpa [E, W, h305ServiceCoordinateCover] using
      h305_serviceNeighborEndpointCover_eq H R Cedge hservice u v huinj hu
        hdisj hcover a i j ha
  have hcapU : serviceNeighborEndpointCover R Cedge a ∩ U = E := by
    rw [hcoverEq]
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hxE | hxW, hxU⟩
      · exact hxE
      · exact (Finset.disjoint_left.mp hd hxU hxW).elim
    · intro hxE
      exact ⟨Or.inl hxE, hEU hxE⟩
  have hcapW : serviceNeighborEndpointCover R Cedge a ∩ W = W := by
    rw [hcoverEq]
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · exact fun hx ↦ hx.2
    · exact fun hxW ↦ ⟨Or.inr hxW, hxW⟩
  constructor
  · rw [edgeIndexedService_sum_neighbor_endpoint_inter_card
      H R Cedge hservice a U, hcapU]
    change E.card = 4
    rw [Finset.card_image_of_injective _ huinj]
    exact h305ServiceEligibleCoordinates_card_four i j hoffset
  · rw [edgeIndexedService_sum_neighbor_endpoint_inter_card
      H R Cedge hservice a W, hcapW]
    change W.card = 8
    rw [Finset.card_image_of_injective _ hvinj]
    decide

end

end Erdos85

#print axioms Erdos85.h305_serviceNeighbor_shore_masses
