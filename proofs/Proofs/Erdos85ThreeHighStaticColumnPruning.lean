import Proofs.Erdos85ThreeHighCompactColumnDFS

namespace Erdos85

def threeHighSingleColumn (j : Fin 8) (S : Finset (Fin 15)) : ThreeHighCross :=
  fun i a => decide (a = j ∧ i ∈ S)

theorem threeHighSingleColumn_subgraph
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (j : Fin 8) :
    EncodedSubgraph
      (threeHighEmptyAdj U R (threeHighSingleColumn j (threeHighCrossColumns cross j)))
      (threeHighEmptyAdj U R cross) := by
  apply threeHighEmptyAdj_subgraph
  intro i a h
  have hh : a = j ∧ cross i j = true := by
    simpa [threeHighSingleColumn,threeHighCrossColumns] using h
  rcases hh with ⟨rfl,h⟩
  exact h

/-- Test each candidate column against the fixed U/R graph before entering DFS. -/
def threeHighStaticPrunedColumnList
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool) (j : Fin 8) :
    List (Finset (Fin 15)) :=
  (threeHighCompactColumnList R j).filter fun S =>
    encodedC4FreeCachedRows (threeHighEmptyAdj U R (threeHighSingleColumn j S))

attribute [local irreducible] threeHighCrossDomain encodedC4Free

theorem threeHighStaticPrunedColumnList_complete
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (hcap : threeHighCrossBlockCap cross = true) (j : Fin 8) :
    threeHighCrossColumns cross j ∈ threeHighStaticPrunedColumnList U R j := by
  apply List.mem_filter.mpr
  refine ⟨threeHighCompactColumnList_complete R j _
    (threeHighCrossColumnDomain_complete U R cross hc hcap j),?_⟩
  rw [encodedC4FreeCachedRows_eq]
  exact encodedC4Free_of_subgraph _ _ (threeHighSingleColumn_subgraph U R cross j)
    ((mem_threeHighCrossDomain_iff U R cross).mp hc).1

end Erdos85
#print axioms Erdos85.threeHighSingleColumn_subgraph
#print axioms Erdos85.threeHighStaticPrunedColumnList_complete
