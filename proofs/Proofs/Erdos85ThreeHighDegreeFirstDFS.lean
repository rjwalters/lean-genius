import Proofs.Erdos85ThreeHighCachedCrossDFS

namespace Erdos85

/-- Cheap degree failures short-circuit before the common-neighbor test. -/
def threeHighDegreeFirstDFS (UAdj : Fin 15 → Fin 15 → Bool)
    (RAdj : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) : Bool :=
  finiteRowDFS (threeHighCrossRowList UAdj)
    (fun k rows =>
      let cross := threeHighCrossOfRows rows
      threeHighCrossCapacity RAdj cross && threeHighCrossCanFill RAdj cross k &&
        encodedC4FreeCachedRows (threeHighEmptyAdj UAdj RAdj cross))
    (fun rows =>
      let cross := threeHighCrossOfRows rows
      encodedDegreeProfile (threeHighEmptyAdj UAdj RAdj cross)
        (fun i => if i = 23 then 6 else 4) && accept cross)
    15 0 (fun _ => ∅)



theorem threeHighDegreeFirstDFS_eq
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) :
    threeHighDegreeFirstDFS UAdj RAdj accept = threeHighCrossPrunedDFS UAdj RAdj accept := by
  rw [← threeHighCachedCrossDFS_eq]
  simp only [threeHighDegreeFirstDFS, threeHighCachedCrossDFS]
  congr 1
  funext k rows
  simp only [Bool.and_assoc, Bool.and_comm]

end Erdos85
#print axioms Erdos85.threeHighDegreeFirstDFS_eq
