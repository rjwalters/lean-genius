import Proofs.Erdos85OrderFortyNineThreeHighTripleCrossEdgeSum

namespace Erdos85
open SimpleGraph
noncomputable section

private theorem rotate_three_labels {V : Type*} [DecidableEq V] (s t v : V) :
    ({s,t,v} : Finset V) = {v,s,t} ∧ ({s,t,v} : Finset V) = {t,s,v} := by
  constructor <;> ext x <;> simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto

theorem threeHigh_triple_three_secondary_edges_deficient_labels
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
      Set (Fin 49))).edgeFinset.card = 3) :
    ∃ a b c : Fin 49, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      threeHighTripleSpecialSet G z = {a,b,c} ∧
      threeHighTripleBlockCrossCount G a b = 5 ∧
      threeHighTripleBlockCrossCount G a c = 5 ∧
      threeHighTripleBlockCrossCount G b c = 4 := by
  classical
  have hl := (threeHigh_triple_union_secondary_edge_ledger G hfree hmin hHigh hone z hz hu huz).1
  have he := threeHigh_triple_union_edges_eq_six_add_cross_counts G hfree hmin hHigh hone z hz
    hu huz s t v hst hsv htv hS
  have hp := threeHigh_triple_cross_count_patterns G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS
  dsimp only at hl hp
  rw [hr] at hl
  have hcases :
      (threeHighTripleBlockCrossCount G s t = 4 ∧ threeHighTripleBlockCrossCount G s v = 5 ∧ threeHighTripleBlockCrossCount G t v = 5) ∨
      (threeHighTripleBlockCrossCount G s t = 5 ∧ threeHighTripleBlockCrossCount G s v = 4 ∧ threeHighTripleBlockCrossCount G t v = 5) ∨
      (threeHighTripleBlockCrossCount G s t = 5 ∧ threeHighTripleBlockCrossCount G s v = 5 ∧ threeHighTripleBlockCrossCount G t v = 4) := by omega
  rcases hcases with h | h | h
  · refine ⟨v,s,t,hsv.symm,htv.symm,hst,?_,?_,?_,h.1⟩
    · exact hS.trans (rotate_three_labels s t v).1
    · rw [threeHighTripleBlockCrossCount_comm]; exact h.2.1
    · rw [threeHighTripleBlockCrossCount_comm]; exact h.2.2
  · refine ⟨t,s,v,hst.symm,htv,hsv,?_,?_,h.2.2,h.2.1⟩
    · exact hS.trans (rotate_three_labels s t v).2
    · rw [threeHighTripleBlockCrossCount_comm]; exact h.1
  · exact ⟨s,t,v,hst,hsv,htv,hS,h⟩

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_three_secondary_edges_deficient_labels
