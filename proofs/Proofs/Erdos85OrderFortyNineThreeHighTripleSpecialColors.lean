import Proofs.Erdos85SaturatedNeighborBijection
import Proofs.Erdos85OrderFortyNineThreeHighTripleBlockCapacity
import Proofs.Erdos85OrderFortyNineThreeHighTripleSecondaryPartition

namespace Erdos85
open SimpleGraph
noncomputable section

/-- The three special roots are paired bijectively with the three high colors. -/
theorem threeHigh_triple_special_color_equiv
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3) :
    ∃ e : (↑(threeHighTripleSpecialSet G z) : Set (Fin 49)) ≃
        (↑(orderFortyNineHighVertices G) : Set (Fin 49)),
      ∀ s h, G.Adj s.val h.val ↔ e s = h := by
  classical
  let S := threeHighTripleSpecialSet G z
  let H := orderFortyNineHighVertices G
  have hS : S.card = 3 := threeHigh_triple_special_singleton_count G hfree hmin hHigh z hz
  have hs (s : Fin 49) (hs : s ∈ S) : (G.neighborFinset s ∩ H).card = 1 :=
    (Finset.mem_filter.mp hs).2
  have hcap : ∀ h ∈ H, (G.neighborFinset h ∩ S).card ≤ 1 := by
    intro h hh
    apply neighbor_block_inter_card_le_one G hfree z S (Finset.filter_subset _ _)
    intro he
    have hzero := orderFortyNine_highNeighborCount_eq_zero_of_high G hfree hmin (Fintype.card_fin 49) hh
    change (orderFortyNineHighSupport G h).card = 0 at hzero
    rw [he, hz] at hzero
    contradiction
  have hmass : (∑ s ∈ S, (G.neighborFinset s ∩ H).card) = S.card := by
    calc
      (∑ s ∈ S, (G.neighborFinset s ∩ H).card) = ∑ _s ∈ S, 1 :=
        Finset.sum_congr rfl (fun s hs' => hs s hs')
      _ = S.card := by simp
  exact saturated_neighbor_blocks_equiv G S H (hS.trans hHigh.symm)
    (fun s hs' => le_of_eq (hs s hs')) hcap hmass

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_special_color_equiv
