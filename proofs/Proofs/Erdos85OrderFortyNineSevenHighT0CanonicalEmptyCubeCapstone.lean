import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeSemanticCover
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeSplitTerminal

/-! # Final H7 empty-cube evidence composition -/

namespace Erdos85

/-- Exact certificate-facing H7 capstone: one direct or binary-tree LRAT
evidence value for each of the `19/15/7/2` canonical empty cubes excludes the
entire seven-high stratum. -/
theorem orderFortyNineStratumExcluded_seven_of_emptyCubeEvidenceVectors
    (e6 : ∀ i : Fin 19,
      SevenHighT0CanonicalEmptyCubeLratEvidence 6 i)
    (e7 : ∀ i : Fin 15,
      SevenHighT0CanonicalEmptyCubeLratEvidence 7 i)
    (e8 : ∀ i : Fin 7,
      SevenHighT0CanonicalEmptyCubeLratEvidence 8 i)
    (e9 : ∀ i : Fin 2,
      SevenHighT0CanonicalEmptyCubeLratEvidence 9 i) :
    OrderFortyNineStratumExcluded 7 :=
  orderFortyNineStratumExcluded_seven_of_emptyCubeChecks
    sevenHighT0CanonicalEmptyCubeSemanticCover
    (sevenHighT0CanonicalEmptyCubeCheckedProvider_of_evidenceVectors
      e6 e7 e8 e9)

end Erdos85

#print axioms Erdos85.orderFortyNineStratumExcluded_seven_of_emptyCubeEvidenceVectors
