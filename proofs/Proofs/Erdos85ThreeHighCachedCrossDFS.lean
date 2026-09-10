import Proofs.Erdos85ThreeHighCrossPrunedDFS
import Proofs.Erdos85EncodedC4CachedRows

namespace Erdos85

def threeHighCachedCrossDFS (UAdj : Fin 15 → Fin 15 → Bool)
    (RAdj : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) : Bool :=
  finiteRowDFS (threeHighCrossRowList UAdj)
    (fun k rows =>
      let cross := threeHighCrossOfRows rows
      encodedC4FreeCachedRows (threeHighEmptyAdj UAdj RAdj cross) &&
        threeHighCrossCapacity RAdj cross && threeHighCrossCanFill RAdj cross k)
    (fun rows =>
      let cross := threeHighCrossOfRows rows
      encodedDegreeProfile (threeHighEmptyAdj UAdj RAdj cross)
        (fun i => if i = 23 then 6 else 4) && accept cross)
    15 0 (fun _ => ∅)


theorem threeHighCachedCrossDFS_eq
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) :
    threeHighCachedCrossDFS UAdj RAdj accept = threeHighCrossPrunedDFS UAdj RAdj accept := by
  simp only [threeHighCachedCrossDFS, threeHighCrossPrunedDFS, encodedC4FreeCachedRows_eq]

end Erdos85
#print axioms Erdos85.threeHighCachedCrossDFS_eq
