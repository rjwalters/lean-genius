import Proofs.Erdos85ThreeHighBlockResolution
import Proofs.Erdos85OrderFortyNineThreeHighTripleResolution
import Proofs.Erdos85OrderFortyNineThreeHighTripleCanonicalColorResiduals

namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_actual_block_search
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z h s : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    (hh : h ∈ orderFortyNineHighVertices G)
    (hs : s ∈ G.neighborFinset h) (hsz : G.Adj s z)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (B : Fin 24 → Fin 24 → Bool)
    (hB : ∀ i j, decide (G.Adj (e i).val (e j).val) = B i j)
    (roots : Fin 3 → Fin 49) (hroots : ∀ k, roots k ∈ threeHighTripleSpecialSet G z)
    (blocks : Fin 3 → Finset (Fin 24))
    (hblocks : ∀ k, blocks k = threeHighSingletonCoordinates G e (roots k)) :
    let C := fun x => threeHighSingletonCoordinates G e x
    threeHighBlockResolutionSearch B (Finset.univ \ (C z ∪ C s)) blocks = true := by
  classical
  apply threeHighBlockResolutionSearch_of_mem B _ blocks _
    (threeHigh_triple_coordinate_resolution_mem G hfree hmin hHigh hone z h s hz hh hs hsz e B hB)
  intro S hS
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hS
  have hcover := threeHigh_triple_ordinary_color_cover G hfree hmin hHigh hone z h s hz hh hs hsz
  have hxd := hcover.2.1 x hx
  have hh8 : G.degree h = 8 := (Finset.mem_filter.mp hh).2
  have hx7 := orderFortyNine_neighbor_degree_seven_of_degreeEight G hfree hmin
    (Fintype.card_fin 49) hh8 ((G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hx).1)
  have hxnz : ¬ G.Adj x z := by
    intro ha
    have hd := threeHigh_triple_empty_neighbor_degree G hfree hmin hHigh hone z hz hx7
    change (G.neighborFinset x ∩ threeHighTripleEmptySet G).card + _ = _ at hd
    rw [hxd.1, hxd.2, if_pos ha] at hd
    omega
  exact threeHigh_triple_coordinate_block_gate G hfree e z x hxnz roots hroots blocks hblocks

theorem threeHigh_triple_actual_canonical_block_search
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z h s : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    (hh : h ∈ orderFortyNineHighVertices G)
    (hs : s ∈ G.neighborFinset h) (hsz : G.Adj s z)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (B : Fin 24 → Fin 24 → Bool)
    (hB : ∀ i j, decide (G.Adj (e i).val (e j).val) = B i j)
    (roots : Fin 3 → Fin 49) (hroots : ∀ k, roots k ∈ threeHighTripleSpecialSet G z)
    (hrows : ∀ k i, (e (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (k,i)))).val ∈
      G.neighborFinset (roots k) ∩ threeHighTripleEmptySet G) :
    let C := fun x => threeHighSingletonCoordinates G e x
    threeHighBlockResolutionSearch B (Finset.univ \ (C z ∪ C s)) threeHighCanonicalRow = true := by
  apply threeHigh_triple_actual_block_search G hfree hmin hHigh hone z h s hz hh hs hsz e B hB
    roots hroots threeHighCanonicalRow
  intro k
  exact (threeHigh_triple_special_coordinates_eq_row G hfree hmin hHigh hone z hz
    (hroots k) e k (hrows k)).symm

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_actual_block_search
#print axioms Erdos85.threeHigh_triple_actual_canonical_block_search
