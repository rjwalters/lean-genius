import Proofs.Erdos85OrderFortyNineHighNeighborLowPartition
import Proofs.Erdos85OrderFortyNineThreeHighTripleSecondaryPartition

/-! The six ordinary singleton blocks of one high color form an exact cover. -/
set_option maxHeartbeats 2000000
namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_ordinary_color_cover
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ v, 7 ≤ G.degree v)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z h s : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    (hh : h ∈ orderFortyNineHighVertices G)
    (hs : s ∈ G.neighborFinset h) (hsz : G.Adj s z) :
    let E := threeHighTripleEmptySet G
    let O := G.neighborFinset h \ {z,s}
    let R := E \ ((G.neighborFinset z ∩ E) ∪ (G.neighborFinset s ∩ E))
    O.card = 6 ∧
    (∀ x ∈ O, (orderFortyNineHighSupport G x).card = 1 ∧
      (G.neighborFinset x ∩ E).card = 3) ∧
    (∀ x ∈ O, ∀ y ∈ O, x ≠ y →
      Disjoint (G.neighborFinset x ∩ E) (G.neighborFinset y ∩ E)) ∧
    O.biUnion (fun x => G.neighborFinset x ∩ E) = R ∧ R.card = 18 := by
  classical
  let E := threeHighTripleEmptySet G
  let O := G.neighborFinset h \ {z,s}
  let R := E \ ((G.neighborFinset z ∩ E) ∪ (G.neighborFinset s ∩ E))
  change O.card = 6 ∧ (∀ x ∈ O, (orderFortyNineHighSupport G x).card = 1 ∧
    (G.neighborFinset x ∩ E).card = 3) ∧
    (∀ x ∈ O, ∀ y ∈ O, x ≠ y → Disjoint (G.neighborFinset x ∩ E) (G.neighborFinset y ∩ E)) ∧
    O.biUnion (fun x => G.neighborFinset x ∩ E) = R ∧ R.card = 18
  have hh8 : G.degree h = 8 := (Finset.mem_filter.mp hh).2
  have hzH : orderFortyNineHighSupport G z = orderFortyNineHighVertices G :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (le_of_eq (hHigh.trans hz.symm))
  have hzh : G.Adj z h := by
    have hm : h ∈ orderFortyNineHighSupport G z := by rw [hzH]; exact hh
    exact (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hm).1
  have hzN : z ∈ G.neighborFinset h := (G.mem_neighborFinset _ _).mpr hzh.symm
  have hzs : z ≠ s := hsz.ne.symm
  have hK : ({z,s} : Finset (Fin 49)) ⊆ G.neighborFinset h := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hzN
    · exact Finset.mem_singleton.mp hx ▸ hs
  have hO : O.card = 6 := by
    dsimp [O]
    rw [Finset.card_sdiff_of_subset hK, G.card_neighborFinset_eq_degree, hh8]
    simp [hzs]
  have hxN {x} (hx : x ∈ O) : x ∈ G.neighborFinset h := (Finset.mem_sdiff.mp hx).1
  have hxz {x} (hx : x ∈ O) : x ≠ z := by
    intro heq
    exact (Finset.mem_sdiff.mp hx).2 (by simp [heq])
  have hxs {x} (hx : x ∈ O) : x ≠ s := by
    intro heq
    exact (Finset.mem_sdiff.mp hx).2 (by simp [heq])
  have hdegrees : ∀ x ∈ O, (orderFortyNineHighSupport G x).card = 1 ∧
      (G.neighborFinset x ∩ E).card = 3 := by
    intro x hx
    have hle := threeHigh_triple_other_support_le_one G hfree hmin hHigh z hz (hxz hx)
    have hpos : 0 < (orderFortyNineHighSupport G x).card := by
      apply Finset.card_pos.mpr
      exact ⟨h, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        ((G.mem_neighborFinset _ _).mp (hxN hx)).symm, hh⟩⟩
    have hx1 : (orderFortyNineHighSupport G x).card = 1 := by omega
    have hx7 := orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin (Fintype.card_fin 49) hh8 ((G.mem_neighborFinset _ _).mp (hxN hx))
    have hnot : ¬ G.Adj x z := by
      intro ha
      have hc := (not_containsC4_iff_forall_common_le_one G).mp hfree h z hzh.ne.symm
      have hxc : x ∈ G.neighborFinset h ∩ G.neighborFinset z :=
        Finset.mem_inter.mpr ⟨hxN hx,(G.mem_neighborFinset _ _).mpr ha.symm⟩
      have hsc : s ∈ G.neighborFinset h ∩ G.neighborFinset z :=
        Finset.mem_inter.mpr ⟨hs,(G.mem_neighborFinset _ _).mpr hsz.symm⟩
      exact hxs hx (Finset.card_le_one.mp hc x hxc s hsc)
    have hd := threeHigh_triple_empty_neighbor_degree G hfree hmin hHigh hone z hz hx7
    change (G.neighborFinset x ∩ E).card + _ = _ at hd
    rw [hx1, if_neg hnot] at hd
    exact ⟨hx1, by omega⟩
  obtain ⟨hcover,hdis⟩ := orderFortyNine_high_neighbor_low_partition G hfree hmin
    (Fintype.card_fin 49) E (Finset.filter_subset _ _) hh
  have hdisO : ∀ x ∈ O, ∀ y ∈ O, x ≠ y →
      Disjoint (G.neighborFinset x ∩ E) (G.neighborFinset y ∩ E) := by
    intro x hx y hy hxy
    exact hdis x (hxN hx) y (hxN hy) hxy
  have hrest : O.biUnion (fun x => G.neighborFinset x ∩ E) = R := by
    apply Finset.ext
    intro v
    constructor
    · intro hv
      obtain ⟨x,hx,hvx⟩ := Finset.mem_biUnion.mp hv
      apply Finset.mem_sdiff.mpr
      refine ⟨(Finset.mem_inter.mp hvx).2, ?_⟩
      intro hm
      rcases Finset.mem_union.mp hm with hvz | hvs
      · exact Finset.disjoint_left.mp (hdis x (hxN hx) z hzN (hxz hx)) hvx hvz
      · exact Finset.disjoint_left.mp (hdis x (hxN hx) s hs (hxs hx)) hvx hvs
    · intro hv
      have hp := Finset.mem_sdiff.mp hv
      have hvcover : v ∈ (G.neighborFinset h).biUnion (fun x => G.neighborFinset x ∩ E) := by
        rw [hcover]; exact hp.1
      obtain ⟨x,hx,hvx⟩ := Finset.mem_biUnion.mp hvcover
      refine Finset.mem_biUnion.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hx, ?_⟩, hvx⟩
      intro hm
      rcases Finset.mem_insert.mp hm with rfl | hm
      · exact hp.2 (Finset.mem_union_left _ hvx)
      · have heq := Finset.mem_singleton.mp hm
        subst x
        exact hp.2 (Finset.mem_union_right _ hvx)
  refine ⟨hO,hdegrees,hdisO,hrest,?_⟩
  rw [← hrest, Finset.card_biUnion (show (↑O : Set (Fin 49)).Pairwise
    (fun x y => Disjoint (G.neighborFinset x ∩ E) (G.neighborFinset y ∩ E)) from hdisO)]
  calc
    (∑ x ∈ O, (G.neighborFinset x ∩ E).card) = ∑ _x ∈ O, 3 :=
      Finset.sum_congr rfl (fun x hx => (hdegrees x hx).2)
    _ = 18 := by simp [hO]

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_ordinary_color_cover
