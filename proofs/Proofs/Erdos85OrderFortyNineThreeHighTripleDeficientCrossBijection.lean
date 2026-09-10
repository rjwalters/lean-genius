import Proofs.Erdos85DeficientNeighborBijection
import Proofs.Erdos85OrderFortyNineThreeHighTripleCrossCounts

/-! A four-edge special-block matching omits exactly one endpoint per block. -/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_cross_count_four_equiv
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {s t : Fin 49} (hs : s ∈ threeHighTripleSpecialSet G z)
    (ht : t ∈ threeHighTripleSpecialSet G z)
    (hcount : threeHighTripleBlockCrossCount G s t = 4) :
    let A := G.neighborFinset s ∩ threeHighTripleEmptySet G
    let B := G.neighborFinset t ∩ threeHighTripleEmptySet G
    ∃ a ∈ A, ∃ b ∈ B,
      (∀ x ∈ A, (G.neighborFinset x ∩ B).card = 0 ↔ x = a) ∧
      (∀ y ∈ B, (G.neighborFinset y ∩ A).card = 0 ↔ y = b) ∧
      ∃ e : (↑(A.erase a) : Set (Fin 49)) ≃ (↑(B.erase b) : Set (Fin 49)),
        ∀ (x : (↑(A.erase a) : Set (Fin 49))) (y : (↑(B.erase b) : Set (Fin 49))),
          G.Adj x.val y.val ↔ e x = y := by
  classical
  let A := G.neighborFinset s ∩ threeHighTripleEmptySet G
  let B := G.neighborFinset t ∩ threeHighTripleEmptySet G
  change ∃ a ∈ A, ∃ b ∈ B,
    (∀ x ∈ A, (G.neighborFinset x ∩ B).card = 0 ↔ x = a) ∧
    (∀ y ∈ B, (G.neighborFinset y ∩ A).card = 0 ↔ y = b) ∧
    ∃ e : (↑(A.erase a) : Set (Fin 49)) ≃ (↑(B.erase b) : Set (Fin 49)),
      ∀ (x : (↑(A.erase a) : Set (Fin 49))) (y : (↑(B.erase b) : Set (Fin 49))),
        G.Adj x.val y.val ↔ e x = y
  have hs1 := (Finset.mem_filter.mp hs).2
  have ht1 := (Finset.mem_filter.mp ht).2
  have hsz := ((G.mem_neighborFinset z s).mp (Finset.mem_filter.mp hs).1).symm
  have htz := ((G.mem_neighborFinset z t).mp (Finset.mem_filter.mp ht).1).symm
  have hAc : A.card = 5 := threeHigh_triple_special_empty_count G hfree hmin hHigh hone z hz hs1 hsz
  have hBc : B.card = 5 := threeHigh_triple_special_empty_count G hfree hmin hHigh hone z hz ht1 htz
  have hA : ∀ x ∈ A, (G.neighborFinset x ∩ B).card ≤ 1 := by
    intro x hx
    apply neighbor_block_inter_card_le_one G hfree t B Finset.inter_subset_left
    intro he
    have hx0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
    subst x
    omega
  have hB : ∀ y ∈ B, (G.neighborFinset y ∩ A).card ≤ 1 := by
    intro y hy
    apply neighbor_block_inter_card_le_one G hfree s A Finset.inter_subset_left
    intro he
    have hy0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
    subst y
    omega
  have hmass : (∑ x ∈ A, (G.neighborFinset x ∩ B).card) + 1 = A.card := by
    rw [sum_card_neighbor_inter_comm G A B, hAc]
    change threeHighTripleBlockCrossCount G s t + 1 = 5
    omega
  exact deficient_neighbor_blocks_equiv G A B (hAc.trans hBc.symm) hA hB hmass

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_cross_count_four_equiv
