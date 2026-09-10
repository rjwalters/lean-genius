import Proofs.Erdos85ThreeHighCanonicalTripleShapes
import Proofs.Erdos85ThreeHighPrunedJointResolution
import Proofs.Erdos85ThreeHighCrossPrunedDFS

namespace Erdos85

/-- Compute the three graph-specific triple lists before entering family callbacks. -/
def threeHighCanonicalShapeSearch (B : Fin 24 → Fin 24 → Bool) : Bool :=
  let D0 := (threeHighCanonicalTripleShapes 0).filter (threeHighTripleNoCommonNeighbor B)
  let D1 := (threeHighCanonicalTripleShapes 1).filter (threeHighTripleNoCommonNeighbor B)
  let D2 := (threeHighCanonicalTripleShapes 2).filter (threeHighTripleNoCommonNeighbor B)
  finitePivotFamilySearch D0 (fun F =>
    finitePrunedFamilySearch D1
      (fun chosen => encodedFamilyIntersectionCap chosen F)
      (fun K => threeHighFamilyPairCompatible B F K &&
        finitePrunedFamilySearch D2
          (fun chosen => encodedFamilyIntersectionCap chosen (F ∪ K))
          (fun L => threeHighFamilyPairCompatible B F L &&
            threeHighFamilyPairCompatible B K L)
          6 (threeHighCanonicalResidual 2) ∅)
      6 (threeHighCanonicalResidual 1) ∅)
    6 (threeHighCanonicalResidual 0) ∅

/-- Exact Boolean equality permits either search to discharge the same certificate. -/
theorem threeHighCanonicalShapeSearch_eq (B : Fin 24 → Fin 24 → Bool) :
    threeHighCanonicalShapeSearch B =
      threeHighPrunedJointResolutionSearch B threeHighCanonicalResidual threeHighCanonicalRow := by
  simp only [threeHighCanonicalShapeSearch, threeHighCanonicalTripleShapes_filter,
    threeHighPrunedJointResolutionSearch, threeHighBlockFamilySearch,
    threeHighPrunedBlockFamilySearch]

/-- The factored terminal can be used directly in any U/R search certificate. -/
def threeHighCanonicalShapeCrossSearch
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool) : Bool :=
  threeHighCrossPrunedDFS UAdj RAdj fun cross =>
    threeHighCanonicalShapeSearch (threeHighEmptyAdj UAdj RAdj cross)

theorem threeHighCanonicalShapeCrossSearch_eq
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool) :
    threeHighCanonicalShapeCrossSearch UAdj RAdj =
      threeHighCrossPrunedDFS UAdj RAdj (fun cross =>
        threeHighPrunedJointResolutionSearch (threeHighEmptyAdj UAdj RAdj cross)
          threeHighCanonicalResidual threeHighCanonicalRow) := by
  simp only [threeHighCanonicalShapeCrossSearch, threeHighCanonicalShapeSearch_eq]

end Erdos85
#print axioms Erdos85.threeHighCanonicalShapeSearch_eq

#print axioms Erdos85.threeHighCanonicalShapeCrossSearch_eq
