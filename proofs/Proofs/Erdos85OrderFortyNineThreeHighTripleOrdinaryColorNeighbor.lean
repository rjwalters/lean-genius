import Proofs.Erdos85OrderFortyNineThreeHighTripleSecondaryPartition
import Proofs.Erdos85OrderFortyNineEmptyNeighborhoodCompatibility

/-! Ordinary singleton vertices have compatible ordinary neighbors of every high color. -/
namespace Erdos85
open SimpleGraph
noncomputable section

private theorem positive_support_degree_seven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ v, 7 ≤ G.degree v)
    {x : Fin 49} (hx : 0 < (orderFortyNineHighSupport G x).card) : G.degree x = 7 := by
  rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (Fintype.card_fin 49) x with h | h
  · exact h
  · have hm : x ∈ orderFortyNineHighVertices G := by simp [orderFortyNineHighVertices, h]
    have hz := orderFortyNine_highNeighborCount_eq_zero_of_high G hfree hmin (Fintype.card_fin 49) hm
    change (orderFortyNineHighSupport G x).card = 0 at hz
    omega

theorem threeHigh_triple_positive_support_no_special_neighbor
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {x s : Fin 49} (hx : 0 < (orderFortyNineHighSupport G x).card) (hxz : x ≠ z)
    (hs : s ∈ threeHighTripleSpecialSet G z) : ¬ G.Adj x s := by
  intro hxs
  have hs1 := (Finset.mem_filter.mp hs).2
  have hs7 := positive_support_degree_seven G hfree hmin (show 0 < (orderFortyNineHighSupport G s).card by omega)
  have hsz := ((G.mem_neighborFinset z s).mp (Finset.mem_filter.mp hs).1).symm
  have hd := orderFortyNine_graphNeighbor_highSupports_pairwiseDisjoint G hfree hmin
    (Fintype.card_fin 49) hs7 ((G.mem_neighborFinset s x).mpr hxs.symm)
    ((G.mem_neighborFinset s z).mpr hsz) hxz
  have hsub : orderFortyNineHighSupport G x ∪ orderFortyNineHighSupport G z ⊆
      orderFortyNineHighVertices G := Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, hz, hHigh] at hc
  omega

theorem threeHigh_triple_ordinary_empty_degree_three
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {x : Fin 49} (hx : (orderFortyNineHighSupport G x).card = 1) (hxz : ¬ G.Adj x z) :
    (G.neighborFinset x ∩ threeHighTripleEmptySet G).card = 3 := by
  have hx7 := positive_support_degree_seven G hfree hmin (show 0 < (orderFortyNineHighSupport G x).card by omega)
  have hh := threeHigh_triple_empty_neighbor_degree G hfree hmin hHigh hone z hz hx7
  rw [hx, if_neg hxz] at hh
  change (G.neighborFinset x ∩ threeHighTripleEmptySet G).card + 1 = 4 + 2 * 0 at hh
  omega

theorem threeHigh_triple_ordinary_exists_compatible_color_neighbor
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {x h : Fin 49} (hx : (orderFortyNineHighSupport G x).card = 1)
    (hxz : ¬ G.Adj x z) (hh : h ∈ orderFortyNineHighVertices G) :
    ∃ y, y ≠ x ∧ G.degree y = 7 ∧ (orderFortyNineHighSupport G y).card = 1 ∧
      ¬ G.Adj y z ∧ G.Adj x y ∧ G.Adj y h ∧
      (G.neighborFinset y ∩ threeHighTripleEmptySet G).card = 3 ∧
      ∀ a ∈ threeHighTripleEmptySet G, ∀ b ∈ threeHighTripleEmptySet G,
        G.Adj x a → G.Adj y b → ¬ G.Adj a b := by
  classical
  let E := threeHighTripleEmptySet G
  let forbidden := insert z (threeHighTripleSpecialSet G z)
  have hx7 := positive_support_degree_seven G hfree hmin (show 0 < (orderFortyNineHighSupport G x).card by omega)
  have hxne : x ≠ z := by intro he; subst x; omega
  have hxE : x ∉ E := by
    intro he
    have hx0 := (Finset.mem_filter.mp he).2
    omega
  have hE : ∀ v ∈ E, (G.neighborFinset v ∩ orderFortyNineHighVertices G).card = 0 := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hforbidden : ∀ s ∈ forbidden, ¬ G.Adj x s := by
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hxz
    · exact threeHigh_triple_positive_support_no_special_neighbor G hfree hmin hHigh z hz
        (show 0 < (orderFortyNineHighSupport G x).card by omega) hxne hs
  obtain ⟨y, hyx, hy7, hyE, hyF, hxy, hyh, hcompat⟩ :=
    orderFortyNine_exists_compatible_high_color_neighbor G hfree hmin (Fintype.card_fin 49)
      E forbidden hE hx7 hxE hh hforbidden
  have hyz : y ≠ z := by intro he; exact hyF (Finset.mem_insert.mpr (Or.inl he))
  have hyle := threeHigh_triple_other_support_le_one G hfree hmin hHigh z hz hyz
  have hypos : 0 < (orderFortyNineHighSupport G y).card := Finset.card_pos.mpr
    ⟨h, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y h).mpr hyh, hh⟩⟩
  have hy1 : (orderFortyNineHighSupport G y).card = 1 := by omega
  have hynz : ¬ G.Adj y z := by
    intro ha
    apply hyF
    apply Finset.mem_insert_of_mem
    exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset z y).mpr ha.symm, hy1⟩
  exact ⟨y, hyx, hy7, hy1, hynz, hxy, hyh,
    threeHigh_triple_ordinary_empty_degree_three G hfree hmin hHigh hone z hz hy1 hynz, hcompat⟩

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_positive_support_no_special_neighbor
#print axioms Erdos85.threeHigh_triple_ordinary_empty_degree_three
#print axioms Erdos85.threeHigh_triple_ordinary_exists_compatible_color_neighbor
