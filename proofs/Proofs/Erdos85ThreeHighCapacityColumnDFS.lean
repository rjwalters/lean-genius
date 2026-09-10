import Proofs.Erdos85ThreeHighColumnRowCapacity
import Proofs.Erdos85ThreeHighCompactColumnDFS

namespace Erdos85

/-- Column search with caller-supplied complete domains and cached U degrees. -/
def threeHighCapacityColumnDFSWith
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (lists : Fin 8 → List (Finset (Fin 15))) (accept : ThreeHighCross → Bool) : Bool :=
  let domains := Array.ofFn lists
  let degrees := Array.ofFn (fun i : Fin 15 => encodedRowDegree (U i))
  finiteRowDFS (fun j => domains[j.val]!)
    (fun k columns =>
      let cross := threeHighCrossOfColumns columns
      threeHighColumnRowCapacityFor (fun i => degrees[i.val]!) cross k &&
        encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow &&
        encodedC4FreeCachedRows (threeHighEmptyAdj U R cross))
    (fun columns =>
      let cross := threeHighCrossOfColumns columns
      encodedDegreeProfile (threeHighEmptyAdj U R cross) (fun i => if i = 23 then 6 else 4) &&
        accept cross)
    8 0 (fun _ => ∅)

private theorem prefix_encode (cross : ThreeHighCross) (k : Nat) :
    threeHighCrossOfColumns (finiteRowPrefix (fun _ => ∅) (threeHighCrossColumns cross) k) =
      threeHighCrossColumnPrefix cross k := by
  funext i j
  by_cases hj : j.val < k <;>
    simp [threeHighCrossOfColumns,finiteRowPrefix,threeHighCrossColumns,threeHighCrossColumnPrefix,hj]

attribute [local irreducible] threeHighCrossDomain encodedC4Free encodedDegreeProfile

theorem threeHighCapacityColumnDFSWith_witness
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (lists : Fin 8 → List (Finset (Fin 15))) (accept : ThreeHighCross → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true)
    (hlist : ∀ j, threeHighCrossColumns cross j ∈ lists j)
    (ha : accept cross = true) : threeHighCapacityColumnDFSWith U R lists accept = true := by
  simp only [threeHighCapacityColumnDFSWith]
  apply finiteRowDFS_witness _ _ _ (fun _ => ∅) (threeHighCrossColumns cross)
  · intro j
    simpa using hlist j
  · intro k hk
    rw [prefix_encode]
    simp only [Bool.and_eq_true,encodedC4FreeCachedRows_eq]
    have hsub := threeHighCrossColumnPrefix_subgraph U R cross k
    refine ⟨⟨?_,encodedExternalBlockCap_mono _ _ _ hsub hExt⟩,
      encodedC4Free_of_subgraph _ _ hsub ((mem_threeHighCrossDomain_iff U R cross).mp hc).1⟩
    simpa [threeHighColumnRowCapacity] using threeHighCrossDomain_column_prefix_capacity U R cross hc k
  · rw [threeHighCrossOfColumns_columns]
    simp only [Bool.and_eq_true]
    exact ⟨((mem_threeHighCrossDomain_iff U R cross).mp hc).2,ha⟩

def threeHighCapacityColumnDFS : ThreeHighExternalSearch := fun U R accept =>
  threeHighCapacityColumnDFSWith U R (threeHighCompactColumnList R) accept

theorem threeHighCapacityColumnDFS_sound : ThreeHighExternalSearchSound threeHighCapacityColumnDFS := by
  intro U R accept cross hc hExt ha
  apply threeHighCapacityColumnDFSWith_witness U R _ accept cross hc hExt _ ha
  have hcap := hExt
  rw [threeHighExternalBlockCap_factor] at hcap
  simp only [Bool.and_eq_true] at hcap
  intro j
  exact threeHighCompactColumnList_complete R j _
    (threeHighCrossColumnDomain_complete U R cross hc hcap.2 j)

end Erdos85
#print axioms Erdos85.threeHighCapacityColumnDFSWith_witness
#print axioms Erdos85.threeHighCapacityColumnDFS_sound
