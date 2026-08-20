import Proofs.Erdos85EdgeIndexedServiceTypeHandshake
import Proofs.Erdos85MuNegThreeZeroFiveServiceShoreTypeProfiles

/-! # Cross-shore h305 service profiles -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

def h305CrossServiceEligibleCoordinates (i : ZMod 8) : Finset (ZMod 8) :=
  Finset.univ.filter fun k ↦ i ≠ k - 1 ∧ i ≠ k + 1

set_option maxRecDepth 100000 in
theorem h305CrossServiceEligibleCoordinates_card_six
    : ∀ i : ZMod 8, (h305CrossServiceEligibleCoordinates i).card = 6 := by
  native_decide

/-- A cross-shore central edge excludes precisely the two cycle neighbors of
its endpoint on each shore. -/
theorem h305_cross_serviceNeighborEndpointCover_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, v j}) :
    serviceNeighborEndpointCover R Cedge a =
      (h305CrossServiceEligibleCoordinates i).image u ∪
        (h305CrossServiceEligibleCoordinates j).image v := by
  classical
  rw [edgeIndexedService_neighborEndpointCover_eq H R Cedge hservice a]
  ext x
  rcases hcover x with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image]
    have hnotV : ¬ ∃ q ∈ h305CrossServiceEligibleCoordinates j, v q = u k := by
      rintro ⟨q, hq, hqu⟩
      exact hdisj k q hqu.symm
    rw [or_iff_left hnotV]
    constructor
    · intro hz
      refine ⟨k, ?_, rfl⟩
      rw [Finset.card_eq_zero] at hz
      simp only [h305CrossServiceEligibleCoordinates, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro hi
        have hadj : H.Adj (u k) (u i) := by
          apply (H.mem_neighborFinset (u k) (u i)).mp
          rw [hu k]
          exact Finset.mem_insert.mpr (Or.inl (congrArg u hi))
        have hm : u i ∈ internalEndpointNeighborFinset H R (u k) a := by
          apply Finset.mem_filter.mpr
          exact ⟨by rw [ha]; simp, hadj⟩
        rw [hz] at hm
        exact Finset.notMem_empty _ hm
      · intro hi
        have hadj : H.Adj (u k) (u i) := by
          apply (H.mem_neighborFinset (u k) (u i)).mp
          rw [hu k]
          exact Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr (congrArg u hi)))
        have hm : u i ∈ internalEndpointNeighborFinset H R (u k) a := by
          apply Finset.mem_filter.mpr
          exact ⟨by rw [ha]; simp, hadj⟩
        rw [hz] at hm
        exact Finset.notMem_empty _ hm
    · rintro ⟨q, hq, hqu⟩
      have hk : k ∈ h305CrossServiceEligibleCoordinates i := huinj hqu ▸ hq
      rw [Finset.card_eq_zero]
      ext y
      simp only [internalEndpointNeighborFinset, Finset.mem_filter,
        Finset.notMem_empty, iff_false, not_and]
      intro hya hadj
      rw [ha] at hya
      simp only [Finset.mem_insert, Finset.mem_singleton] at hya
      rcases hya with rfl | rfl
      · have hm := (H.mem_neighborFinset (u k) (u i)).mpr hadj
        rw [hu k] at hm
        rcases Finset.mem_insert.mp hm with hm | hm
        · exact (Finset.mem_filter.mp hk).2.1 (huinj hm)
        · exact (Finset.mem_filter.mp hk).2.2
            (huinj (Finset.mem_singleton.mp hm))
      · have hm := (H.mem_neighborFinset (u k) (v j)).mpr hadj
        rw [hu k] at hm
        rcases Finset.mem_insert.mp hm with hm | hm
        · exact hdisj (k - 1) j hm.symm
        · exact hdisj (k + 1) j (Finset.mem_singleton.mp hm).symm
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image]
    have hnotU : ¬ ∃ q ∈ h305CrossServiceEligibleCoordinates i, u q = v k := by
      rintro ⟨q, hq, hqv⟩
      exact hdisj q k hqv
    rw [or_iff_right hnotU]
    constructor
    · intro hz
      refine ⟨k, ?_, rfl⟩
      rw [Finset.card_eq_zero] at hz
      simp only [h305CrossServiceEligibleCoordinates, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro hj
        have hadj : H.Adj (v k) (v j) := by
          apply (H.mem_neighborFinset (v k) (v j)).mp
          rw [hv k]
          exact Finset.mem_insert.mpr (Or.inl (congrArg v hj))
        have hm : v j ∈ internalEndpointNeighborFinset H R (v k) a :=
          Finset.mem_filter.mpr
          ⟨by rw [ha]; simp, hadj⟩
        rw [hz] at hm
        exact Finset.notMem_empty _ hm
      · intro hj
        have hadj : H.Adj (v k) (v j) := by
          apply (H.mem_neighborFinset (v k) (v j)).mp
          rw [hv k]
          exact Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr (congrArg v hj)))
        have hm : v j ∈ internalEndpointNeighborFinset H R (v k) a :=
          Finset.mem_filter.mpr
          ⟨by rw [ha]; simp, hadj⟩
        rw [hz] at hm
        exact Finset.notMem_empty _ hm
    · rintro ⟨q, hq, hqv⟩
      have hk : k ∈ h305CrossServiceEligibleCoordinates j := hvinj hqv ▸ hq
      rw [Finset.card_eq_zero]
      ext y
      simp only [internalEndpointNeighborFinset, Finset.mem_filter,
        Finset.notMem_empty, iff_false, not_and]
      intro hya hadj
      rw [ha] at hya
      simp only [Finset.mem_insert, Finset.mem_singleton] at hya
      rcases hya with rfl | rfl
      · have hm := (H.mem_neighborFinset (v k) (u i)).mpr hadj
        rw [hv k] at hm
        rcases Finset.mem_insert.mp hm with hm | hm
        · exact hdisj i (k - 1) hm
        · exact hdisj i (k + 1) (Finset.mem_singleton.mp hm)
      · have hm := (H.mem_neighborFinset (v k) (v j)).mpr hadj
        rw [hv k] at hm
        rcases Finset.mem_insert.mp hm with hm | hm
        · exact (Finset.mem_filter.mp hk).2.1 (hvinj hm)
        · exact (Finset.mem_filter.mp hk).2.2
            (hvinj (Finset.mem_singleton.mp hm))

/-- Cross-shore central service stars have one of four symmetric profiles. -/
theorem h305_cross_serviceNeighbor_shoreType_profiles
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, v j}) :
    let U := Finset.univ.image u
    let x := serviceNeighborShoreTypeCount R Cedge a U 2
    let y := serviceNeighborShoreTypeCount R Cedge a U 1
    let z := serviceNeighborShoreTypeCount R Cedge a U 0
    (x = 0 ∧ y = 6 ∧ z = 0) ∨ (x = 1 ∧ y = 4 ∧ z = 1) ∨
      (x = 2 ∧ y = 2 ∧ z = 2) ∨ (x = 3 ∧ y = 0 ∧ z = 3) := by
  classical
  dsimp only
  let U : Finset V := Finset.univ.image u
  let W : Finset V := Finset.univ.image v
  let EU : Finset V := (h305CrossServiceEligibleCoordinates i).image u
  let EW : Finset V := (h305CrossServiceEligibleCoordinates j).image v
  have hd : Disjoint U W := by
    rw [Finset.disjoint_left]
    intro q hqU hqW
    rcases Finset.mem_image.mp hqU with ⟨k, -, rfl⟩
    rcases Finset.mem_image.mp hqW with ⟨l, -, h⟩
    exact hdisj k l h.symm
  have hEU : EU ⊆ U := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨k, hk, rfl⟩
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  have hcoverEq : serviceNeighborEndpointCover R Cedge a = EU ∪ EW := by
    simpa [EU, EW] using h305_cross_serviceNeighborEndpointCover_eq
      H R Cedge hservice u v huinj hvinj hu hv hdisj hcover a i j ha
  have hcapU : serviceNeighborEndpointCover R Cedge a ∩ U = EU := by
    rw [hcoverEq]
    ext q
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hq | hq, hU⟩
      · exact hq
      · have hW : q ∈ W := by
          rcases Finset.mem_image.mp hq with ⟨k, hk, rfl⟩
          exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
        exact (Finset.disjoint_left.mp hd hU hW).elim
    · intro hq
      exact ⟨Or.inl hq, hEU hq⟩
  have hmass : (serviceNeighborEndpointCover R Cedge a ∩ U).card = 6 := by
    rw [hcapU]
    rw [Finset.card_image_of_injective _ huinj]
    exact h305CrossServiceEligibleCoordinates_card_six i
  let x := serviceNeighborShoreTypeCount R Cedge a U 2
  let y := serviceNeighborShoreTypeCount R Cedge a U 1
  let z := serviceNeighborShoreTypeCount R Cedge a U 0
  have htypes := edgeIndexedService_shoreMass_eq_typeCounts
    H R Cedge hservice a U
  have htotal := edgeIndexedService_shoreTypeCounts_sum R Cedge a U
  have hdegree : (Cedge.neighborFinset a).card = 6 := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hCreg a
  change (x = 0 ∧ y = 6 ∧ z = 0) ∨ (x = 1 ∧ y = 4 ∧ z = 1) ∨
    (x = 2 ∧ y = 2 ∧ z = 2) ∨ (x = 3 ∧ y = 0 ∧ z = 3)
  change (serviceNeighborEndpointCover R Cedge a ∩ U).card =
    2 * x + y at htypes
  change (Cedge.neighborFinset a).card = z + y + x at htotal
  omega

end

end Erdos85

#print axioms Erdos85.h305_cross_serviceNeighbor_shoreType_profiles
