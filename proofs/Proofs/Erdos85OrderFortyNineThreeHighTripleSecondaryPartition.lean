import Proofs.Erdos85OrderFortyNineThreeHighTripleSpecialBlocks

/-! Actual 1+15+8 secondary partition of the H3 triple empty set. -/
namespace Erdos85
open SimpleGraph
noncomputable section
variable (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]

noncomputable def threeHighTripleEmptySet : Finset (Fin 49) := by
  classical
  exact (orderFortyNineLowVertices G).filter fun x => (orderFortyNineHighSupport G x).card = 0
noncomputable def threeHighTripleSpecialSet (z : Fin 49) : Finset (Fin 49) := by
  classical
  exact (G.neighborFinset z).filter fun x => (orderFortyNineHighSupport G x).card = 1
noncomputable def threeHighTripleSpecialUnion (z : Fin 49) : Finset (Fin 49) := by
  classical
  exact (threeHighTripleSpecialSet G z).biUnion fun s => G.neighborFinset s ∩ threeHighTripleEmptySet G

variable [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  (hfree : ¬ containsC4 (Fin 49) G)
  (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
  (hHigh : (orderFortyNineHighVertices G).card = 3)
  (hone : orderFortyNineHighIncidenceCount G 3 = 1)
include hfree hmin hHigh hone

private theorem empty_member_degree_seven {u : Fin 49}
    (hu : u ∈ threeHighTripleEmptySet G) : G.degree u = 7 := by
  have hulow := (Finset.mem_filter.mp hu).1
  rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (Fintype.card_fin 49) u with h | h
  · exact h
  · exact ((Finset.mem_sdiff.mp hulow).2 (by simp [orderFortyNineHighVertices, h])).elim

theorem threeHigh_triple_root_empty_outside_special_union
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z) :
    u ∉ threeHighTripleSpecialUnion G z := by
  classical
  intro hm
  obtain ⟨s, hs, hus⟩ := Finset.mem_biUnion.mp hm
  have hs1 := (Finset.mem_filter.mp hs).2
  have hsu : G.Adj s u := (G.mem_neighborFinset s u).mp (Finset.mem_inter.mp hus).1
  have hzs : z ≠ s := by intro heq; rw [← heq, hz] at hs1; omega
  have hd := orderFortyNine_graphNeighbor_highSupports_pairwiseDisjoint G hfree hmin
    (Fintype.card_fin 49) (empty_member_degree_seven G hfree hmin hHigh hone hu)
    ((G.mem_neighborFinset u z).mpr huz) ((G.mem_neighborFinset u s).mpr hsu.symm) hzs
  have hsub : orderFortyNineHighSupport G z ∪ orderFortyNineHighSupport G s ⊆
      orderFortyNineHighVertices G := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact (Finset.mem_inter.mp hw).2
    · exact (Finset.mem_inter.mp hw).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, hz, hs1, hHigh] at hc
  omega

theorem threeHigh_triple_root_empty_no_special_union_edge
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    {x : Fin 49} (hx : x ∈ threeHighTripleSpecialUnion G z) : ¬ G.Adj u x := by
  classical
  obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.mp hx
  have hs1 := (Finset.mem_filter.mp hs).2
  have hu0 := (Finset.mem_filter.mp hu).2
  have hus : u ≠ s := by intro heq; rw [heq, hs1] at hu0; omega
  have hsz : G.Adj s z := ((G.mem_neighborFinset z s).mp (Finset.mem_filter.mp hs).1).symm
  intro hux
  have hc := (not_containsC4_iff_forall_common_le_one G).mp hfree u s hus
  have hxcom : x ∈ G.neighborFinset u ∩ G.neighborFinset s :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u x).mpr hux, (Finset.mem_inter.mp hxs).1⟩
  have hzcom : z ∈ G.neighborFinset u ∩ G.neighborFinset s :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u z).mpr huz, (G.mem_neighborFinset s z).mpr hsz⟩
  have hxz := Finset.card_le_one.mp hc x hxcom z hzcom
  have hx0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hxs).2).2
  rw [hxz, hz] at hx0
  omega

theorem threeHigh_triple_secondary_partition
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z) :
    let E := threeHighTripleEmptySet G
    let U := threeHighTripleSpecialUnion G z
    let R := E \ insert u U
    let N := G.neighborFinset u ∩ E
    U.card = 15 ∧ u ∉ U ∧ R.card = 8 ∧ N ⊆ R ∧ N.card = 6 ∧ (R \ N).card = 2 := by
  classical
  let E := threeHighTripleEmptySet G
  let U := threeHighTripleSpecialUnion G z
  let R := E \ insert u U
  let N := G.neighborFinset u ∩ E
  change U.card = 15 ∧ u ∉ U ∧ R.card = 8 ∧ N ⊆ R ∧ N.card = 6 ∧ (R \ N).card = 2
  have hU : U.card = 15 := threeHigh_triple_special_empty_union_card G hfree hmin hHigh hone z hz
  have huU : u ∉ U := threeHigh_triple_root_empty_outside_special_union G hfree hmin hHigh hone z hz hu huz
  have hE : E.card = 24 := (threeHigh_t1_global_incidence G hfree hmin hHigh hone).1
  have hsub : insert u U ⊆ E := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hu
    · obtain ⟨s, hs, hx⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_inter.mp hx).2
  have hR : R.card = 8 := by
    dsimp [R]
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_insert_of_notMem huU, hU, hE]
  have hNR : N ⊆ R := by
    intro x hx
    apply Finset.mem_sdiff.mpr
    refine ⟨(Finset.mem_inter.mp hx).2, ?_⟩
    intro hm
    rcases Finset.mem_insert.mp hm with hxu | hxU
    · have ha := (G.mem_neighborFinset u x).mp (Finset.mem_inter.mp hx).1
      exact ha.ne hxu.symm
    · exact threeHigh_triple_root_empty_no_special_union_edge G hfree hmin hHigh hone z hz hu huz hxU
        ((G.mem_neighborFinset u x).mp (Finset.mem_inter.mp hx).1)
  have hN : N.card = 6 := by
    have h := threeHigh_triple_empty_neighbor_degree G hfree hmin hHigh hone z hz
      (empty_member_degree_seven G hfree hmin hHigh hone hu)
    have hu0 := (Finset.mem_filter.mp hu).2
    rw [hu0, Nat.add_zero, if_pos huz] at h
    exact h
  refine ⟨hU, huU, hR, hNR, hN, ?_⟩
  rw [Finset.card_sdiff_of_subset hNR, hR, hN]

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_root_empty_outside_special_union
#print axioms Erdos85.threeHigh_triple_root_empty_no_special_union_edge
#print axioms Erdos85.threeHigh_triple_secondary_partition
