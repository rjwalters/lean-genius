import Proofs.Erdos85FiniteRowDFS
import Proofs.Erdos85ThreeHighCrossRows
import Proofs.Erdos85ThreeHighCrossCapacity

namespace Erdos85

def threeHighCrossRowList (UAdj : Fin 15 → Fin 15 → Bool) (i : Fin 15) :
    List (Finset (Fin 8)) :=
  ((List.finRange 8).sublists.map List.toFinset).filter fun S =>
    S.card = 4 - encodedRowDegree (UAdj i)

theorem threeHighCrossRowList_complete
    (UAdj : Fin 15 → Fin 15 → Bool) (i : Fin 15) (S : Finset (Fin 8))
    (hS : S ∈ threeHighCrossRowDomain UAdj i) : S ∈ threeHighCrossRowList UAdj i := by
  have hc := (Finset.mem_powersetCard.mp hS).2
  apply List.mem_filter.mpr
  refine ⟨?_, by simpa using hc⟩
  apply List.mem_map.mpr
  let l := (List.finRange 8).filter fun j => j ∈ S
  have he : l.toFinset = S := by
    ext j
    simp [l]
  refine ⟨l, List.mem_sublists.mpr ?_, he⟩
  exact List.filter_sublist

def threeHighCrossDFS (UAdj : Fin 15 → Fin 15 → Bool)
    (RAdj : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) : Bool :=
  finiteRowDFS (threeHighCrossRowList UAdj)
    (fun _ rows => encodedC4Free (threeHighEmptyAdj UAdj RAdj (threeHighCrossOfRows rows)) &&
      threeHighCrossCapacity RAdj (threeHighCrossOfRows rows))
    (fun rows => accept (threeHighCrossOfRows rows)) 15 0 (fun _ => ∅)

private theorem prefix_encode (cross : ThreeHighCross) (k : ℕ) :
    threeHighCrossOfRows (finiteRowPrefix (fun _ => ∅) (threeHighCrossRows cross) k) =
      threeHighCrossPrefix cross k := by
  funext i j
  by_cases hi : i.val < k <;>
    simp [threeHighCrossOfRows, finiteRowPrefix, threeHighCrossRows, threeHighCrossPrefix, hi]

attribute [local irreducible] threeHighCrossDomain encodedC4Free encodedDegreeProfile
  threeHighCrossCapacity threeHighCrossRowDomain

theorem threeHighCrossDFS_witness
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain UAdj RAdj) (ha : accept cross = true) :
    threeHighCrossDFS UAdj RAdj accept = true := by
  apply finiteRowDFS_witness _ _ _ (fun _ => ∅) (threeHighCrossRows cross)
  · intro i
    exact threeHighCrossRowList_complete UAdj i _
      ((threeHighCrossDomain_rows UAdj RAdj cross hc).2 i)
  · intro k hk
    rw [prefix_encode]
    simp only [Bool.and_eq_true]
    exact ⟨threeHighCrossDomain_prefix_c4 UAdj RAdj cross hc k,
      threeHighCrossDomain_prefix_capacity UAdj RAdj cross hc k⟩
  · simpa only [threeHighCrossOfRows_rows] using ha

theorem threeHighCrossDFS_reject
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) (hfalse : threeHighCrossDFS UAdj RAdj accept = false) :
    ∀ cross ∈ threeHighCrossDomain UAdj RAdj, accept cross = false := by
  intro cross hc
  cases ha : accept cross
  · rfl
  · have h := threeHighCrossDFS_witness UAdj RAdj accept cross hc ha
    rw [hfalse] at h
    contradiction

end Erdos85
#print axioms Erdos85.threeHighCrossRowList_complete
#print axioms Erdos85.threeHighCrossDFS_witness
#print axioms Erdos85.threeHighCrossDFS_reject
