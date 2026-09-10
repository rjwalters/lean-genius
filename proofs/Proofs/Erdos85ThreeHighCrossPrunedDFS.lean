import Proofs.Erdos85ThreeHighCrossDFS
import Proofs.Erdos85ThreeHighCrossDeficit

namespace Erdos85

/-- Incidence search with both degree bounds during construction and exact degrees
before the supplied terminal test. -/
def threeHighCrossPrunedDFS (UAdj : Fin 15 → Fin 15 → Bool)
    (RAdj : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) : Bool :=
  finiteRowDFS (threeHighCrossRowList UAdj)
    (fun k rows =>
      let cross := threeHighCrossOfRows rows
      encodedC4Free (threeHighEmptyAdj UAdj RAdj cross) &&
        threeHighCrossCapacity RAdj cross && threeHighCrossCanFill RAdj cross k)
    (fun rows =>
      let cross := threeHighCrossOfRows rows
      encodedDegreeProfile (threeHighEmptyAdj UAdj RAdj cross)
        (fun i => if i = 23 then 6 else 4) && accept cross)
    15 0 (fun _ => ∅)

private theorem prefix_encode (cross : ThreeHighCross) (k : ℕ) :
    threeHighCrossOfRows (finiteRowPrefix (fun _ => ∅) (threeHighCrossRows cross) k) =
      threeHighCrossPrefix cross k := by
  funext i j
  by_cases hi : i.val < k <;>
    simp [threeHighCrossOfRows, finiteRowPrefix, threeHighCrossRows, threeHighCrossPrefix, hi]

attribute [local irreducible] threeHighCrossDomain encodedC4Free encodedDegreeProfile
  threeHighCrossCapacity threeHighCrossCanFill threeHighCrossRowDomain

theorem threeHighCrossPrunedDFS_witness
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain UAdj RAdj) (ha : accept cross = true) :
    threeHighCrossPrunedDFS UAdj RAdj accept = true := by
  apply finiteRowDFS_witness _ _ _ (fun _ => ∅) (threeHighCrossRows cross)
  · intro i
    exact threeHighCrossRowList_complete UAdj i _
      ((threeHighCrossDomain_rows UAdj RAdj cross hc).2 i)
  · intro k hk
    rw [prefix_encode]
    simp only [Bool.and_eq_true]
    exact ⟨⟨threeHighCrossDomain_prefix_c4 UAdj RAdj cross hc k,
      threeHighCrossDomain_prefix_capacity UAdj RAdj cross hc k⟩,
      threeHighCrossDomain_prefix_canFill UAdj RAdj cross hc k⟩
  · rw [threeHighCrossOfRows_rows]
    simp only [Bool.and_eq_true]
    exact ⟨((mem_threeHighCrossDomain_iff UAdj RAdj cross).mp hc).2, ha⟩

theorem threeHighCrossPrunedDFS_reject
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) (hfalse : threeHighCrossPrunedDFS UAdj RAdj accept = false) :
    ∀ cross ∈ threeHighCrossDomain UAdj RAdj, accept cross = false := by
  intro cross hc
  cases ha : accept cross
  · rfl
  · have h := threeHighCrossPrunedDFS_witness UAdj RAdj accept cross hc ha
    rw [hfalse] at h
    contradiction

end Erdos85
#print axioms Erdos85.threeHighCrossPrunedDFS_witness
#print axioms Erdos85.threeHighCrossPrunedDFS_reject
