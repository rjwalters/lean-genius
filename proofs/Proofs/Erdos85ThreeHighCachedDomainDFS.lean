import Proofs.Erdos85ThreeHighExternalSearchCertificate

namespace Erdos85

/-- Materialize each row domain once, retaining its original list order. -/
def threeHighCachedDomainDFS (UAdj : Fin 15 → Fin 15 → Bool)
    (RAdj : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) : Bool :=
  let domains := Array.ofFn (threeHighRootPrunedRowList UAdj)
  let fixedCap := threeHighUnionBlockCap UAdj
  finiteRowDFS (fun i => domains[i.val]!)
    (fun k rows =>
      let cross := threeHighCrossOfRows rows
      threeHighCrossCapacity RAdj cross &&
        threeHighCrossAvailableCanFill RAdj cross k threeHighUBlock &&
        (fixedCap && threeHighCrossBlockCap cross) &&
        encodedC4FreeCachedRows (threeHighEmptyAdj UAdj RAdj cross))
    (fun rows =>
      let cross := threeHighCrossOfRows rows
      encodedDegreeProfile (threeHighEmptyAdj UAdj RAdj cross)
        (fun i => if i = 23 then 6 else 4) && accept cross)
    15 0 (fun _ => ∅)

theorem threeHighCachedDomainDFS_eq
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) :
    threeHighCachedDomainDFS U R accept = threeHighAvailableBlockDFS U R accept := by
  simp [threeHighCachedDomainDFS,threeHighAvailableBlockDFS]

attribute [local irreducible] threeHighCrossDomain

theorem threeHighCachedDomainDFS_sound :
    ThreeHighExternalSearchSound threeHighCachedDomainDFS := by
  intro U R accept cross hc hExt ha
  rw [threeHighCachedDomainDFS_eq]
  exact threeHighAvailableBlockDFS_sound U R accept cross hc hExt ha

end Erdos85
#print axioms Erdos85.threeHighCachedDomainDFS_eq
#print axioms Erdos85.threeHighCachedDomainDFS_sound
