import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyDegrees

/-! The three disjoint five-vertex special blocks in the H3 triple profile. -/
namespace Erdos85
open SimpleGraph
noncomputable section

variable (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  (hfree : ¬ containsC4 (Fin 49) G)
  (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
  (hHigh : (orderFortyNineHighVertices G).card = 3)
include hfree hmin hHigh

theorem threeHigh_triple_other_support_le_one
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {x : Fin 49} (hxz : x ≠ z) :
    (orderFortyNineHighSupport G x).card ≤ 1 := by
  classical
  have hzH : orderFortyNineHighSupport G z = orderFortyNineHighVertices G := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    exact le_of_eq (hHigh.trans hz.symm)
  have hcommon := (not_containsC4_iff_forall_common_le_one G).mp hfree x z hxz
  have hsub : orderFortyNineHighSupport G x ⊆ G.neighborFinset x ∩ G.neighborFinset z := by
    intro w hw
    have hp := Finset.mem_inter.mp hw
    have hwz : w ∈ orderFortyNineHighSupport G z := by rw [hzH]; exact hp.2
    exact Finset.mem_inter.mpr ⟨hp.1, (Finset.mem_inter.mp hwz).1⟩
  exact (Finset.card_le_card hsub).trans hcommon

private theorem support_three_degree_seven
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3) : G.degree z = 7 := by
  rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (Fintype.card_fin 49) z with h | h
  · exact h
  · have hzH : z ∈ orderFortyNineHighVertices G := by simp [orderFortyNineHighVertices, h]
    have hzero := orderFortyNine_highNeighborCount_eq_zero_of_high G hfree hmin (Fintype.card_fin 49) hzH
    change (orderFortyNineHighSupport G z).card = 0 at hzero
    omega

theorem threeHigh_triple_special_singleton_count
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3) :
    ((G.neighborFinset z).filter fun x => (orderFortyNineHighSupport G x).card = 1).card = 3 := by
  classical
  have hz7 := support_three_degree_seven G hfree hmin hHigh z hz
  have hs := orderFortyNine_sum_highIncidence_over_lowNeighborhood G hfree hmin (Fintype.card_fin 49) hz7
  change (∑ x ∈ G.neighborFinset z, (orderFortyNineHighSupport G x).card) = _ at hs
  rw [hHigh] at hs
  have hid : (∑ x ∈ G.neighborFinset z, (orderFortyNineHighSupport G x).card) =
      ∑ x ∈ G.neighborFinset z, if (orderFortyNineHighSupport G x).card = 1 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    have hne : x ≠ z := ((G.mem_neighborFinset z x).mp hx).ne.symm
    have hle := threeHigh_triple_other_support_le_one G hfree hmin hHigh z hz hne
    by_cases h1 : (orderFortyNineHighSupport G x).card = 1
    · simp [h1]
    · have h0 : (orderFortyNineHighSupport G x).card = 0 := by omega
      simp [h0]
  rw [hid, ← Finset.card_filter] at hs
  exact hs

theorem threeHigh_triple_special_empty_count
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {s : Fin 49} (hs : (orderFortyNineHighSupport G s).card = 1)
    (hsz : G.Adj s z) :
    (G.neighborFinset s ∩ ((orderFortyNineLowVertices G).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0)).card = 5 := by
  have hs7 : G.degree s = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (Fintype.card_fin 49) s with h | h
    · exact h
    · have hsH : s ∈ orderFortyNineHighVertices G := by simp [orderFortyNineHighVertices, h]
      have hzero := orderFortyNine_highNeighborCount_eq_zero_of_high G hfree hmin (Fintype.card_fin 49) hsH
      change (orderFortyNineHighSupport G s).card = 0 at hzero
      omega
  have h := threeHigh_triple_empty_neighbor_degree G hfree hmin hHigh hone z hz hs7
  rw [hs, if_pos hsz] at h
  omega

theorem threeHigh_triple_special_empty_blocks_disjoint
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {s t : Fin 49} (hst : s ≠ t) (hsz : G.Adj s z) (htz : G.Adj t z) :
    Disjoint (G.neighborFinset s ∩ ((orderFortyNineLowVertices G).filter fun x =>
      (orderFortyNineHighSupport G x).card = 0))
      (G.neighborFinset t ∩ ((orderFortyNineLowVertices G).filter fun x =>
        (orderFortyNineHighSupport G x).card = 0)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hxcom : x ∈ G.neighborFinset s ∩ G.neighborFinset t :=
    Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hy).1⟩
  have hzcom : z ∈ G.neighborFinset s ∩ G.neighborFinset t :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset s z).mpr hsz, (G.mem_neighborFinset t z).mpr htz⟩
  have hc := (not_containsC4_iff_forall_common_le_one G).mp hfree s t hst
  have hxz := Finset.card_le_one.mp hc x hxcom z hzcom
  have hx0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
  rw [hxz, hz] at hx0
  omega


theorem threeHigh_triple_special_empty_union_card
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3) :
    let S := (G.neighborFinset z).filter fun x => (orderFortyNineHighSupport G x).card = 1
    let E := (orderFortyNineLowVertices G).filter fun x => (orderFortyNineHighSupport G x).card = 0
    (S.biUnion fun s => G.neighborFinset s ∩ E).card = 15 := by
  classical
  let S := (G.neighborFinset z).filter fun x => (orderFortyNineHighSupport G x).card = 1
  let E := (orderFortyNineLowVertices G).filter fun x => (orderFortyNineHighSupport G x).card = 0
  change (S.biUnion fun s => G.neighborFinset s ∩ E).card = 15
  have hS : S.card = 3 := threeHigh_triple_special_singleton_count G hfree hmin hHigh z hz
  have hd : (↑S : Set (Fin 49)).Pairwise (fun s t => Disjoint
      (G.neighborFinset s ∩ E) (G.neighborFinset t ∩ E)) := by
    intro s hs t ht hst
    exact threeHigh_triple_special_empty_blocks_disjoint G hfree hmin hHigh z hz hst
      (((G.mem_neighborFinset z s).mp (Finset.mem_filter.mp hs).1).symm)
      (((G.mem_neighborFinset z t).mp (Finset.mem_filter.mp ht).1).symm)
  rw [Finset.card_biUnion hd]
  calc
    (∑ s ∈ S, (G.neighborFinset s ∩ E).card) = ∑ _s ∈ S, 5 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact threeHigh_triple_special_empty_count G hfree hmin hHigh hone z hz
        (Finset.mem_filter.mp hs).2
        (((G.mem_neighborFinset z s).mp (Finset.mem_filter.mp hs).1).symm)
    _ = 15 := by simp [hS]

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_other_support_le_one
#print axioms Erdos85.threeHigh_triple_special_singleton_count
#print axioms Erdos85.threeHigh_triple_special_empty_count
#print axioms Erdos85.threeHigh_triple_special_empty_blocks_disjoint

#print axioms Erdos85.threeHigh_triple_special_empty_union_card
