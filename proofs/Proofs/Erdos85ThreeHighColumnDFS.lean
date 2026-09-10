import Proofs.Erdos85ThreeHighCrossColumns
import Proofs.Erdos85ThreeHighExternalSearchCertificate

namespace Erdos85

def threeHighCrossColumnList (R : Fin 8 → Fin 8 → Bool) (j : Fin 8) : List (Finset (Fin 15)) :=
  ((List.finRange 15).sublists.map List.toFinset).filter fun S =>
    decide (S.card + encodedRowDegree (R j) + (if j.val < 6 then 1 else 0) = 4 ∧
      ∀ k : Fin 3, (S.filter fun i => ((@finProdFinEquiv 3 5).symm i).1 = k).card ≤ 1)

theorem threeHighCrossColumnList_complete (R : Fin 8 → Fin 8 → Bool)
    (j : Fin 8) (S : Finset (Fin 15)) (hS : S ∈ threeHighCrossColumnDomain R j) :
    S ∈ threeHighCrossColumnList R j := by
  apply List.mem_filter.mpr
  refine ⟨?_,by simpa only [threeHighCrossColumnDomain,Finset.mem_filter,Finset.mem_univ,
    true_and,decide_eq_true_eq] using hS⟩
  apply List.mem_map.mpr
  let l := (List.finRange 15).filter fun i => i ∈ S
  have he : l.toFinset = S := by ext i; simp [l]
  exact ⟨l,List.mem_sublists.mpr List.filter_sublist,he⟩

def threeHighCrossColumnPrefix (cross : ThreeHighCross) (k : Nat) : ThreeHighCross :=
  fun i j => if j.val < k then cross i j else false

private theorem prefix_encode (cross : ThreeHighCross) (k : Nat) :
    threeHighCrossOfColumns (finiteRowPrefix (fun _ => ∅) (threeHighCrossColumns cross) k) =
      threeHighCrossColumnPrefix cross k := by
  funext i j
  by_cases hj : j.val < k <;>
    simp [threeHighCrossOfColumns,finiteRowPrefix,threeHighCrossColumns,threeHighCrossColumnPrefix,hj]

theorem threeHighCrossColumnPrefix_subgraph
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (k : Nat) :
    EncodedSubgraph (threeHighEmptyAdj U R (threeHighCrossColumnPrefix cross k))
      (threeHighEmptyAdj U R cross) := by
  apply threeHighEmptyAdj_subgraph
  intro i j h
  by_cases hj : j.val < k
  · simpa only [threeHighCrossColumnPrefix,if_pos hj] using h
  · simp only [threeHighCrossColumnPrefix,if_neg hj,Bool.false_eq_true] at h

def threeHighColumnDFS : ThreeHighExternalSearch := fun U R accept =>
  let domains := Array.ofFn (threeHighCrossColumnList R)
  finiteRowDFS (fun j => domains[j.val]!)
    (fun _ columns =>
      let cross := threeHighCrossOfColumns columns
      encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow &&
        encodedC4FreeCachedRows (threeHighEmptyAdj U R cross))
    (fun columns =>
      let cross := threeHighCrossOfColumns columns
      encodedDegreeProfile (threeHighEmptyAdj U R cross) (fun i => if i = 23 then 6 else 4) &&
        accept cross)
    8 0 (fun _ => ∅)

attribute [local irreducible] threeHighCrossDomain encodedC4Free encodedDegreeProfile

theorem threeHighColumnDFS_sound : ThreeHighExternalSearchSound threeHighColumnDFS := by
  intro U R accept cross hc hExt ha
  have hcrossCap := hExt
  rw [threeHighExternalBlockCap_factor] at hcrossCap
  simp only [Bool.and_eq_true] at hcrossCap
  simp only [threeHighColumnDFS]
  apply finiteRowDFS_witness _ _ _ (fun _ => ∅) (threeHighCrossColumns cross)
  · intro j
    simpa using threeHighCrossColumnList_complete R j _
      (threeHighCrossColumnDomain_complete U R cross hc hcrossCap.2 j)
  · intro k hk
    rw [prefix_encode]
    simp only [Bool.and_eq_true,encodedC4FreeCachedRows_eq]
    have hsub := threeHighCrossColumnPrefix_subgraph U R cross k
    exact ⟨encodedExternalBlockCap_mono _ _ _ hsub hExt,
      encodedC4Free_of_subgraph _ _ hsub ((mem_threeHighCrossDomain_iff U R cross).mp hc).1⟩
  · rw [threeHighCrossOfColumns_columns]
    simp only [Bool.and_eq_true]
    exact ⟨((mem_threeHighCrossDomain_iff U R cross).mp hc).2,ha⟩

end Erdos85
#print axioms Erdos85.threeHighCrossColumnList_complete
#print axioms Erdos85.threeHighCrossColumnPrefix_subgraph
#print axioms Erdos85.threeHighColumnDFS_sound
