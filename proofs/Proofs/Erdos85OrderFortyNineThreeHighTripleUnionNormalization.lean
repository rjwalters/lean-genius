import Proofs.Erdos85ThreeBlockLabels
import Proofs.Erdos85OrderFortyNineThreeHighTripleCrossNormalization

/-! A single fifteen-vertex chart for the actual r4 special-union graph. -/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_four_secondary_edges_union_normalization
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
      (π : Equiv.Perm (Fin 5)),
      (∀ i, (e (0,i)).val ∈ G.neighborFinset s ∩ threeHighTripleEmptySet G) ∧
      (∀ i, (e (1,i)).val ∈ G.neighborFinset t ∩ threeHighTripleEmptySet G) ∧
      (∀ i, (e (2,i)).val ∈ G.neighborFinset v ∩ threeHighTripleEmptySet G) ∧
      (∀ i j, G.Adj (e (0,i)).val (e (1,j)).val ↔ i = j) ∧
      (∀ i j, G.Adj (e (0,i)).val (e (2,j)).val ↔ i = j) ∧
      (∀ i j, G.Adj (e (1,i)).val (e (2,j)).val ↔ π i = j) := by
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
  refine ⟨e,π,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [he0]
    exact (l0 i).property
  · intro i
    rw [he1]
    exact (l1 i).property
  · intro i
    rw [he2]
    exact (l2 i).property
  · intro i j
    rw [he0,he1]
    exact h01 i j
  · intro i j
    rw [he0,he2]
    exact h02 i j
  · intro i j
    rw [he1,he2]
    exact h12 i j

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_four_secondary_edges_union_normalization
