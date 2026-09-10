import Proofs.Erdos85ThreeHighRSwapJointSearch
import Proofs.Erdos85ThreeHighStaticCapacityColumnDFS

namespace Erdos85

/-- Compare a pair only when both of its columns have been assigned. -/
def threeHighRSwapPrefixOrdered (pairs : List (Fin 8 × Fin 8))
    (score : (Fin 15 → Bool) → Nat) (cross : ThreeHighCross) (k : Nat) : Bool :=
  pairs.all fun p => if p.1.val < k ∧ p.2.val < k then
    decide (score (fun i => cross i p.1) ≤ score (fun i => cross i p.2)) else true

theorem threeHighRSwapPrefixOrdered_of_ordered
    (pairs : List (Fin 8 × Fin 8)) (score : (Fin 15 → Bool) → Nat)
    (cross : ThreeHighCross) (ho : threeHighRSwapOrdered pairs score cross = true) (k : Nat) :
    threeHighRSwapPrefixOrdered pairs score (threeHighCrossColumnPrefix cross k) k = true := by
  apply List.all_eq_true.mpr
  intro p hp
  split
  · rename_i h
    have ha : (fun i => threeHighCrossColumnPrefix cross k i p.1) = (fun i => cross i p.1) := by
      funext i
      simp only [threeHighCrossColumnPrefix,if_pos h.1]
    have hb : (fun i => threeHighCrossColumnPrefix cross k i p.2) = (fun i => cross i p.2) := by
      funext i
      simp only [threeHighCrossColumnPrefix,if_pos h.2]
    rw [ha,hb]
    exact List.all_eq_true.mp ho p hp
  · rfl

/-- Column search with caller-supplied complete domains and cached U degrees. -/
def threeHighRSwapColumnDFSWith (pairs : List (Fin 8 × Fin 8))
    (score : (Fin 15 → Bool) → Nat)
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (lists : Fin 8 → List (Finset (Fin 15))) (accept : ThreeHighCross → Bool) : Bool :=
  let domains := Array.ofFn lists
  let degrees := Array.ofFn (fun i : Fin 15 => encodedRowDegree (U i))
  finiteRowDFS (fun j => domains[j.val]!)
    (fun k columns =>
      let cross := threeHighCrossOfColumns columns
      threeHighRSwapPrefixOrdered pairs score cross k &&
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

theorem threeHighRSwapColumnDFSWith_witness (pairs : List (Fin 8 × Fin 8))
    (score : (Fin 15 → Bool) → Nat)
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (lists : Fin 8 → List (Finset (Fin 15))) (accept : ThreeHighCross → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true)
    (hlist : ∀ j, threeHighCrossColumns cross j ∈ lists j)
    (ho : threeHighRSwapOrdered pairs score cross = true)
    (ha : accept cross = true) : threeHighRSwapColumnDFSWith pairs score U R lists accept = true := by
  simp only [threeHighRSwapColumnDFSWith]
  apply finiteRowDFS_witness _ _ _ (fun _ => ∅) (threeHighCrossColumns cross)
  · intro j
    simpa using hlist j
  · intro k hk
    rw [prefix_encode]
    simp only [Bool.and_eq_true,encodedC4FreeCachedRows_eq]
    have hsub := threeHighCrossColumnPrefix_subgraph U R cross k
    refine ⟨⟨⟨threeHighRSwapPrefixOrdered_of_ordered pairs score cross ho k,?_⟩,encodedExternalBlockCap_mono _ _ _ hsub hExt⟩,
      encodedC4Free_of_subgraph _ _ hsub ((mem_threeHighCrossDomain_iff U R cross).mp hc).1⟩
    simpa [threeHighColumnRowCapacity] using threeHighCrossDomain_column_prefix_capacity U R cross hc k
  · rw [threeHighCrossOfColumns_columns]
    simp only [Bool.and_eq_true]
    exact ⟨((mem_threeHighCrossDomain_iff U R cross).mp hc).2,ha⟩

/-- Prune completed swap pairs during column DFS, with joint-specific completeness. -/
def threeHighRSwapColumnJointSearch (pairs : List (Fin 8 × Fin 8))
    (score : (Fin 15 → Bool) → Nat)
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) : ThreeHighJointExternalSearch :=
  fun U R =>
    if threeHighRSwapPairsValid R pairs then
      threeHighRSwapColumnDFSWith pairs score U R (threeHighStaticPrunedColumnList U R)
        (fun c => accept (threeHighEmptyAdj U R c))
    else threeHighStaticCapacityColumnDFS U R (fun c => accept (threeHighEmptyAdj U R c))

theorem threeHighRSwapColumnJointSearch_sound (pairs : List (Fin 8 × Fin 8))
    (score : (Fin 15 → Bool) → Nat)
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (ha : ThreeHighTerminalSound accept) :
    ThreeHighJointExternalSearchSound (threeHighRSwapColumnJointSearch pairs score accept) := by
  intro U R cross hc he hj
  simp only [threeHighRSwapColumnJointSearch]
  split
  · rename_i hv
    obtain ⟨c,hc',he',hj',ho⟩ := threeHighRSwapOrdered_complete U R pairs score hv cross hc he hj
    apply threeHighRSwapColumnDFSWith_witness pairs score U R _ _ c hc' he' _ ho (ha _ hj')
    have hcap := he'
    rw [threeHighExternalBlockCap_factor] at hcap
    simp only [Bool.and_eq_true] at hcap
    intro j
    exact threeHighStaticPrunedColumnList_complete U R c hc' hcap.2 j
  · exact threeHighStaticCapacityColumnDFS_sound U R _ cross hc he (ha _ hj)

end Erdos85
#print axioms Erdos85.threeHighRSwapPrefixOrdered_of_ordered
#print axioms Erdos85.threeHighRSwapColumnDFSWith_witness
#print axioms Erdos85.threeHighRSwapColumnJointSearch_sound
