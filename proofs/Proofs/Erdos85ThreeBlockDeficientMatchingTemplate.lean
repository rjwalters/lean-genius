import Proofs.Erdos85ThreeBlockMatchingTemplate

/-! The explicit identity/identity/deficient-permutation relation used by the r3
finite generator. Its internal rows retain arbitrary matching masks. -/
namespace Erdos85
open SimpleGraph

def threeBlockDeficientMatchingAdj (masks : Fin 3 → BitVec 10) (π : Equiv.Perm (Fin 5)) (d : Fin 5)
    (p q : Fin 3 × Fin 5) : Bool :=
  if p.1 = q.1 then oneHighBranchBitAdj (masks p.1) p.2 q.2
  else if p.1 = 0 ∨ q.1 = 0 then decide (p.2 = q.2)
  else if p.1 = 1 then decide (p.2 ≠ d ∧ π p.2 = q.2)
  else decide (q.2 ≠ d ∧ π q.2 = p.2)

theorem threeBlockDeficientMatchingAdj_eq_graph
    (H : SimpleGraph (Fin 3 × Fin 5)) [DecidableRel H.Adj]
    (π : Equiv.Perm (Fin 5)) (d : Fin 5)
    (h01 : ∀ i j, H.Adj (0,i) (1,j) ↔ i = j)
    (h02 : ∀ i j, H.Adj (0,i) (2,j) ↔ i = j)
    (h12 : ∀ i j, H.Adj (1,i) (2,j) ↔ i ≠ d ∧ π i = j)
    (p q : Fin 3 × Fin 5) :
    decide (H.Adj p q) = threeBlockDeficientMatchingAdj
      (fun k => oneHighBranchGraphEdges (threeBlockRowGraph H k)) π d p q := by
  have h10 (i j : Fin 5) : H.Adj (1,i) (0,j) ↔ i = j :=
    (H.adj_comm _ _).trans ((h01 j i).trans eq_comm)
  have h20 (i j : Fin 5) : H.Adj (2,i) (0,j) ↔ i = j :=
    (H.adj_comm _ _).trans ((h02 j i).trans eq_comm)
  have h21 (i j : Fin 5) : H.Adj (2,i) (1,j) ↔ j ≠ d ∧ π j = i :=
    (H.adj_comm _ _).trans (h12 j i)
  rcases p with ⟨a,i⟩
  rcases q with ⟨b,j⟩
  fin_cases a <;> fin_cases b
  · simp only [threeBlockDeficientMatchingAdj, if_pos rfl]
    rw [oneHighBranchBitAdj_graphEdges_kernel]
    rfl
  · simpa [threeBlockDeficientMatchingAdj] using Bool.decide_congr (h01 i j)
  · simpa [threeBlockDeficientMatchingAdj] using Bool.decide_congr (h02 i j)
  · simpa [threeBlockDeficientMatchingAdj] using Bool.decide_congr (h10 i j)
  · simp only [threeBlockDeficientMatchingAdj, if_pos rfl]
    rw [oneHighBranchBitAdj_graphEdges_kernel]
    rfl
  · change decide (H.Adj (1,i) (2,j)) = decide (i ≠ d ∧ π i = j)
    exact Bool.decide_congr (h12 i j)
  · simpa [threeBlockDeficientMatchingAdj] using Bool.decide_congr (h20 i j)
  · change decide (H.Adj (2,i) (1,j)) = decide (j ≠ d ∧ π j = i)
    exact Bool.decide_congr (h21 i j)
  · simp only [threeBlockDeficientMatchingAdj, if_pos rfl]
    rw [oneHighBranchBitAdj_graphEdges_kernel]
    rfl

end Erdos85
#print axioms Erdos85.threeBlockDeficientMatchingAdj_eq_graph
