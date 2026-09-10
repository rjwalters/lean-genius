import Proofs.Erdos85ThreeHighCompactColumns
import Proofs.Erdos85ThreeHighColumnDFS
import Proofs.Erdos85ThreeHighExternalSearchCertificate

namespace Erdos85

def threeHighCompactColumnList (R : Fin 8 → Fin 8 → Bool) (j : Fin 8) : List (Finset (Fin 15)) :=
  threeHighCompactColumnCandidates.filter fun S =>
    decide (S.card + encodedRowDegree (R j) + (if j.val < 6 then 1 else 0) = 4)

theorem threeHighCompactColumnList_complete (R : Fin 8 → Fin 8 → Bool)
    (j : Fin 8) (S : Finset (Fin 15)) (hS : S ∈ threeHighCrossColumnDomain R j) :
    S ∈ threeHighCompactColumnList R j := by
  have h := (Finset.mem_filter.mp hS).2
  apply List.mem_filter.mpr
  exact ⟨threeHighCompactColumnCandidates_complete S h.2,by simpa using h.1⟩

private theorem prefix_encode (cross : ThreeHighCross) (k : Nat) :
    threeHighCrossOfColumns (finiteRowPrefix (fun _ => ∅) (threeHighCrossColumns cross) k) =
      threeHighCrossColumnPrefix cross k := by
  funext i j
  by_cases hj : j.val < k <;>
    simp [threeHighCrossOfColumns,finiteRowPrefix,threeHighCrossColumns,threeHighCrossColumnPrefix,hj]

def threeHighCompactColumnDFS : ThreeHighExternalSearch := fun U R accept =>
  let domains := Array.ofFn (threeHighCompactColumnList R)
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

theorem threeHighCompactColumnDFS_sound : ThreeHighExternalSearchSound threeHighCompactColumnDFS := by
  intro U R accept cross hc hExt ha
  have hcrossCap := hExt
  rw [threeHighExternalBlockCap_factor] at hcrossCap
  simp only [Bool.and_eq_true] at hcrossCap
  simp only [threeHighCompactColumnDFS]
  apply finiteRowDFS_witness _ _ _ (fun _ => ∅) (threeHighCrossColumns cross)
  · intro j
    simpa using threeHighCompactColumnList_complete R j _
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
#print axioms Erdos85.threeHighCompactColumnList_complete
#print axioms Erdos85.threeHighCompactColumnDFS_sound
