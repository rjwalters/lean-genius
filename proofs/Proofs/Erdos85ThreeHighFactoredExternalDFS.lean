import Proofs.Erdos85ThreeHighExternalBlockFactorization
import Proofs.Erdos85ThreeHighExternalPrefixPruning

namespace Erdos85

/-- Cache the fixed U gate and evaluate the cross-column cap directly. -/
def threeHighFactoredExternalDFS (UAdj : Fin 15 → Fin 15 → Bool)
    (RAdj : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) : Bool :=
  let fixedCap := threeHighUnionBlockCap UAdj
  finiteRowDFS (threeHighRootPrunedRowList UAdj)
    (fun k rows =>
      let cross := threeHighCrossOfRows rows
      threeHighCrossCapacity RAdj cross && threeHighCrossCanFill RAdj cross k &&
        (fixedCap && threeHighCrossBlockCap cross) &&
        encodedC4FreeCachedRows (threeHighEmptyAdj UAdj RAdj cross))
    (fun rows =>
      let cross := threeHighCrossOfRows rows
      encodedDegreeProfile (threeHighEmptyAdj UAdj RAdj cross)
        (fun i => if i = 23 then 6 else 4) && accept cross)
    15 0 (fun _ => ∅)

theorem threeHighFactoredExternalDFS_eq
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) :
    threeHighFactoredExternalDFS UAdj RAdj accept =
      threeHighExternalPrunedDFS UAdj RAdj threeHighCanonicalRow accept := by
  simp only [threeHighFactoredExternalDFS, threeHighExternalPrunedDFS,
    threeHighExternalBlockCap_factor]

attribute [local irreducible] threeHighCrossDomain encodedExternalBlockCap

theorem threeHighFactoredExternalDFS_witness
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain UAdj RAdj)
    (hcap : encodedExternalBlockCap (threeHighEmptyAdj UAdj RAdj cross)
      threeHighCanonicalRow = true) (ha : accept cross = true) :
    threeHighFactoredExternalDFS UAdj RAdj accept = true := by
  rw [threeHighFactoredExternalDFS_eq]
  exact threeHighExternalPrunedDFS_witness UAdj RAdj threeHighCanonicalRow accept cross hc hcap ha

end Erdos85
#print axioms Erdos85.threeHighFactoredExternalDFS_eq
#print axioms Erdos85.threeHighFactoredExternalDFS_witness
