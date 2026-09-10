import Proofs.Erdos85ThreeBlockLabels
import Proofs.Erdos85ThreeBlockMatchingTemplate
import Proofs.Erdos85OrderFortyNineThreeHighTripleInternalDomain
import Proofs.Erdos85OrderFortyNineThreeHighTripleCrossNormalization

/-! A single fifteen-vertex chart for the actual r4 special-union graph. -/
set_option maxHeartbeats 2000000
namespace Erdos85
open SimpleGraph
noncomputable section

private theorem graphBits_mem_congr
    (H K : SimpleGraph (Fin 5)) [hH : DecidableRel H.Adj] [hK : DecidableRel K.Adj]
    (h : H = K) (hm : oneHighBranchGraphEdges K ∈ finFiveTwoEdgeMatchingMasks) :
    oneHighBranchGraphEdges H ∈ finFiveTwoEdgeMatchingMasks := by
  subst K
  cases Subsingleton.elim hH hK
  exact hm

theorem threeHigh_triple_four_secondary_edges_union_template
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (s t v : Fin 49) (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
    (hS : threeHighTripleSpecialSet G z = {s,t,v})
    (hr : (G.induce (↑(threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) :
      Set (Fin 49))).edgeFinset.card = 4) :
    ∃ (e : (Fin 3 × Fin 5) ≃ (↑(threeHighTripleSpecialUnion G z) : Set (Fin 49)))
      (π : Equiv.Perm (Fin 5)) (masks : Fin 3 → BitVec 10),
      (∀ k, masks k ∈ finFiveTwoEdgeMatchingMasks) ∧
      ∀ p q, decide (G.Adj (e p).val (e q).val) = threeBlockMatchingAdj masks π p q := by
  classical
  let A := G.neighborFinset s ∩ threeHighTripleEmptySet G
  let B := G.neighborFinset t ∩ threeHighTripleEmptySet G
  let C := G.neighborFinset v ∩ threeHighTripleEmptySet G
  let U := threeHighTripleSpecialUnion G z
  have hs : s ∈ threeHighTripleSpecialSet G z := by rw [hS]; simp
  have ht : t ∈ threeHighTripleSpecialSet G z := by rw [hS]; simp
  have hv : v ∈ threeHighTripleSpecialSet G z := by rw [hS]; simp
  have hsz := ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hs).1).symm
  have htz := ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp ht).1).symm
  have hvz := ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hv).1).symm
  have hAB : Disjoint A B := threeHigh_triple_special_empty_blocks_disjoint G hfree hmin hHigh z hz hst hsz htz
  have hAC : Disjoint A C := threeHigh_triple_special_empty_blocks_disjoint G hfree hmin hHigh z hz hsv hsz hvz
  have hBC : Disjoint B C := threeHigh_triple_special_empty_blocks_disjoint G hfree hmin hHigh z hz htv htz hvz
  have hU : U = A ∪ B ∪ C := by
    dsimp [U, threeHighTripleSpecialUnion]
    rw [hS]
    simp [A,B,C,Finset.union_assoc]
  obtain ⟨l0,l1,l2,π,h01,h02,h12⟩ := threeHigh_triple_four_secondary_edges_cross_normalization
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  obtain ⟨e,he0,he1,he2⟩ := three_disjoint_block_labels A B C U hU hAB hAC hBC l0 l1 l2
  let H := SimpleGraph.comap (fun p => (e p).val) G
  let masks := fun k => oneHighBranchGraphEdges (threeBlockRowGraph H k)
  have hm0 : masks 0 ∈ finFiveTwoEdgeMatchingMasks := by
    have hm := threeHigh_triple_special_internal_matching_domain G hfree hmin hHigh hone
      z hz hu huz hs l0.symm
    have hg : threeBlockRowGraph H 0 = SimpleGraph.comap l0
        (G.induce (↑A : Set (Fin 49))) := by
      ext i j
      change G.Adj (e (0,i)).val (e (0,j)).val ↔ G.Adj (l0 i).val (l0 j).val
      rw [he0,he0]
    change oneHighBranchGraphEdges (threeBlockRowGraph H 0) ∈ finFiveTwoEdgeMatchingMasks
    exact graphBits_mem_congr _ _ hg hm
  have hm1 : masks 1 ∈ finFiveTwoEdgeMatchingMasks := by
    have hm := threeHigh_triple_special_internal_matching_domain G hfree hmin hHigh hone
      z hz hu huz ht l1.symm
    have hg : threeBlockRowGraph H 1 = SimpleGraph.comap l1
        (G.induce (↑B : Set (Fin 49))) := by
      ext i j
      change G.Adj (e (1,i)).val (e (1,j)).val ↔ G.Adj (l1 i).val (l1 j).val
      rw [he1,he1]
    change oneHighBranchGraphEdges (threeBlockRowGraph H 1) ∈ finFiveTwoEdgeMatchingMasks
    exact graphBits_mem_congr _ _ hg hm
  have hm2 : masks 2 ∈ finFiveTwoEdgeMatchingMasks := by
    have hm := threeHigh_triple_special_internal_matching_domain G hfree hmin hHigh hone
      z hz hu huz hv l2.symm
    have hg : threeBlockRowGraph H 2 = SimpleGraph.comap l2
        (G.induce (↑C : Set (Fin 49))) := by
      ext i j
      change G.Adj (e (2,i)).val (e (2,j)).val ↔ G.Adj (l2 i).val (l2 j).val
      rw [he2,he2]
    change oneHighBranchGraphEdges (threeBlockRowGraph H 2) ∈ finFiveTwoEdgeMatchingMasks
    exact graphBits_mem_congr _ _ hg hm
  have hc01 : ∀ i j, H.Adj (0,i) (1,j) ↔ i = j := by
    intro i j
    change G.Adj (e (0,i)).val (e (1,j)).val ↔ i = j
    rw [he0,he1]
    exact h01 i j
  have hc02 : ∀ i j, H.Adj (0,i) (2,j) ↔ i = j := by
    intro i j
    change G.Adj (e (0,i)).val (e (2,j)).val ↔ i = j
    rw [he0,he2]
    exact h02 i j
  have hc12 : ∀ i j, H.Adj (1,i) (2,j) ↔ π i = j := by
    intro i j
    change G.Adj (e (1,i)).val (e (2,j)).val ↔ π i = j
    rw [he1,he2]
    exact h12 i j
  refine ⟨e,π,masks,?_,?_⟩
  · intro k
    fin_cases k
    · exact hm0
    · exact hm1
    · exact hm2
  · intro p q
    exact threeBlockMatchingAdj_eq_graph H π hc01 hc02 hc12 p q

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_four_secondary_edges_union_template
