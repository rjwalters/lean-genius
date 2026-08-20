import Proofs.Erdos85EdgeIndexedServiceTwoWalkCensus
import Proofs.Erdos85MuNegThreeZeroFiveServiceStarMatching

/-! # Internal two-walk mass in h305 cycle coordinates -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

def zmodEightCycleNeighborCoordinates (k : ZMod 8) : Finset (ZMod 8) :=
  {k - 1, k + 1}

/-- Pure coordinate version of the internal two-walk mass from `k` to the
endpoint pair `{i,j}`. -/
def h305InternalTwoWalkCoordinateMass (i j k : ZMod 8) : ℕ :=
  (zmodEightCycleNeighborCoordinates k ∩
    zmodEightCycleNeighborCoordinates i).card +
  (zmodEightCycleNeighborCoordinates k ∩
    zmodEightCycleNeighborCoordinates j).card

/-- Reindex the abstract H-side of the service two-walk census onto one
labeled h305 eight-cycle. -/
theorem h305_internalEndpointTwoWalkMass_eq_coordinate
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i j k : ZMod 8)
    (hij : i ≠ j)
    (ha : a.1.toFinset = {u i, u j}) :
    internalEndpointTwoWalkMass H R (u k) a =
      h305InternalTwoWalkCoordinateMass i j k := by
  classical
  unfold internalEndpointTwoWalkMass h305InternalTwoWalkCoordinateMass
  rw [Finset.sum_ite]
  simp only [ha]
  simp only [Finset.sum_const_zero, add_zero]
  have hf : Finset.univ.filter (fun x : V ↦ x ∈ ({u i, u j} : Finset V)) =
      {u i, u j} := by ext x; simp
  rw [hf]
  rw [Finset.sum_pair (huinj.ne hij)]
  rw [hu k, hu i, hu j]
  have hinter (p q : ZMod 8) :
      ({u (p - 1), u (p + 1)} ∩ {u (q - 1), u (q + 1)} : Finset V).card =
        (zmodEightCycleNeighborCoordinates p ∩
          zmodEightCycleNeighborCoordinates q).card := by
    let P : Finset (ZMod 8) := zmodEightCycleNeighborCoordinates p
    let Q : Finset (ZMod 8) := zmodEightCycleNeighborCoordinates q
    have hPQ : P.image u ∩ Q.image u = (P ∩ Q).image u := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_inter.mp hx with ⟨hxP, hxQ⟩
        rcases Finset.mem_image.mp hxP with ⟨r, hr, rfl⟩
        rcases Finset.mem_image.mp hxQ with ⟨s, hs, hsu⟩
        exact Finset.mem_image.mpr ⟨r,
          Finset.mem_inter.mpr ⟨hr, huinj hsu.symm ▸ hs⟩, rfl⟩
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_image.mpr ⟨r, (Finset.mem_inter.mp hr).1, rfl⟩,
            Finset.mem_image.mpr ⟨r, (Finset.mem_inter.mp hr).2, rfl⟩⟩
    have hP : ({u (p - 1), u (p + 1)} : Finset V) = P.image u := by
      ext x
      simp [P, zmodEightCycleNeighborCoordinates]
    have hQ : ({u (q - 1), u (q + 1)} : Finset V) = Q.image u := by
      ext x
      simp [Q, zmodEightCycleNeighborCoordinates]
    rw [hP, hQ, hPQ, Finset.card_image_of_injective _ huinj]
  rw [hinter k i, hinter k j]

/-- The service-side incident two-walk mass at a same-shore coordinate is the
explicit cycle-coordinate mass plus four. -/
theorem h305_incidentServiceTwoWalkMass_eq_coordinate_add_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i j k : ZMod 8) (hij : i ≠ j)
    (ha : a.1.toFinset = {u i, u j}) :
    incidentServiceTwoWalkMass R Cedge (u k) a =
      h305InternalTwoWalkCoordinateMass i j k + 4 := by
  rw [edgeIndexedService_twoWalkCensus H R Cedge hservice hHreg hCreg]
  rw [h305_internalEndpointTwoWalkMass_eq_coordinate H R u huinj hu
    a i j k hij ha]

set_option maxRecDepth 100000 in
/-- Exact distribution of H-side two-walk masses on the four eligible
same-shore coordinates.  Offsets `±1` give masses `0,0,1,1`, offsets `±3`
give `1,1,2,2`, and the antipodal offset gives `2,2,2,2`. -/
theorem h305_eligible_internalTwoWalkMass_distribution :
    ∀ i j : ZMod 8,
      let E := h305ServiceEligibleCoordinates i j
      let n := fun t ↦
        (E.filter fun k ↦ h305InternalTwoWalkCoordinateMass i j k = t).card
      ((j - i = 1 ∨ j - i = 7) → n 0 = 2 ∧ n 1 = 2 ∧ n 2 = 0) ∧
      ((j - i = 3 ∨ j - i = 5) → n 0 = 0 ∧ n 1 = 2 ∧ n 2 = 2) ∧
      (j - i = 4 → n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 4) := by
  native_decide

end

end Erdos85

#print axioms Erdos85.h305_internalEndpointTwoWalkMass_eq_coordinate
#print axioms Erdos85.h305_incidentServiceTwoWalkMass_eq_coordinate_add_four
#print axioms Erdos85.h305_eligible_internalTwoWalkMass_distribution
