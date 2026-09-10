import Proofs.Erdos85FinFiveMatchingDomain

/-! The explicit identity/identity/permutation union relation used by the r4
finite generator. Its internal rows retain arbitrary matching masks. -/
namespace Erdos85
open SimpleGraph

def threeBlockRowGraph (H : SimpleGraph (Fin 3 × Fin 5)) (k : Fin 3) :
    SimpleGraph (Fin 5) := SimpleGraph.comap (fun i => (k,i)) H

instance threeBlockRowGraph_decidable
    (H : SimpleGraph (Fin 3 × Fin 5)) [DecidableRel H.Adj] (k : Fin 3) :
    DecidableRel (threeBlockRowGraph H k).Adj := inferInstanceAs
      (DecidableRel (SimpleGraph.comap (fun i => (k,i)) H).Adj)

def threeBlockMatchingAdj (masks : Fin 3 → BitVec 10) (π : Equiv.Perm (Fin 5))
    (p q : Fin 3 × Fin 5) : Bool :=
  if p.1 = q.1 then oneHighBranchBitAdj (masks p.1) p.2 q.2
  else if p.1 = 0 ∨ q.1 = 0 then decide (p.2 = q.2)
  else if p.1 = 1 then decide (π p.2 = q.2)
  else decide (π q.2 = p.2)

theorem threeBlockMatchingAdj_eq_graph
    (H : SimpleGraph (Fin 3 × Fin 5)) [DecidableRel H.Adj]
    (π : Equiv.Perm (Fin 5))
    (h01 : ∀ i j, H.Adj (0,i) (1,j) ↔ i = j)
    (h02 : ∀ i j, H.Adj (0,i) (2,j) ↔ i = j)
    (h12 : ∀ i j, H.Adj (1,i) (2,j) ↔ π i = j)
    (p q : Fin 3 × Fin 5) :
    decide (H.Adj p q) = threeBlockMatchingAdj
      (fun k => oneHighBranchGraphEdges (threeBlockRowGraph H k)) π p q := by
  have h10 (i j : Fin 5) : H.Adj (1,i) (0,j) ↔ i = j :=
    (H.adj_comm _ _).trans ((h01 j i).trans eq_comm)
  have h20 (i j : Fin 5) : H.Adj (2,i) (0,j) ↔ i = j :=
    (H.adj_comm _ _).trans ((h02 j i).trans eq_comm)
  have h21 (i j : Fin 5) : H.Adj (2,i) (1,j) ↔ π j = i :=
    (H.adj_comm _ _).trans (h12 j i)
  rcases p with ⟨a,i⟩
  rcases q with ⟨b,j⟩
  fin_cases a <;> fin_cases b
  · simp only [threeBlockMatchingAdj, if_pos rfl]
    rw [oneHighBranchBitAdj_graphEdges_kernel]
    rfl
  · simpa [threeBlockMatchingAdj] using Bool.decide_congr (h01 i j)
  · simpa [threeBlockMatchingAdj] using Bool.decide_congr (h02 i j)
  · simpa [threeBlockMatchingAdj] using Bool.decide_congr (h10 i j)
  · simp only [threeBlockMatchingAdj, if_pos rfl]
    rw [oneHighBranchBitAdj_graphEdges_kernel]
    rfl
  · simpa [threeBlockMatchingAdj] using Bool.decide_congr (h12 i j)
  · simpa [threeBlockMatchingAdj] using Bool.decide_congr (h20 i j)
  · simpa [threeBlockMatchingAdj] using Bool.decide_congr (h21 i j)
  · simp only [threeBlockMatchingAdj, if_pos rfl]
    rw [oneHighBranchBitAdj_graphEdges_kernel]
    rfl

theorem threeBlockMatchingAdj_row_masks_mem
    (H : SimpleGraph (Fin 3 × Fin 5)) [DecidableRel H.Adj]
    (hdegree : ∀ k i, (threeBlockRowGraph H k).degree i ≤ 1)
    (hedges : ∀ k, (threeBlockRowGraph H k).edgeFinset.card = 2) :
    ∀ k, oneHighBranchGraphEdges (threeBlockRowGraph H k) ∈ finFiveTwoEdgeMatchingMasks := by
  intro k
  exact finFive_two_edge_graph_mem_matching_masks _ (hdegree k) (hedges k)

end Erdos85
#print axioms Erdos85.threeBlockMatchingAdj_eq_graph
#print axioms Erdos85.threeBlockMatchingAdj_row_masks_mem
