import Proofs.Erdos85ColorTripleSupportStabilization
import Proofs.Erdos85ThreeHighListedJointSearch

namespace Erdos85

/-- The no-common-neighbor gate only removes entries from the 536 canonical shapes. -/
theorem threeHighCanonicalSupportSize_le (B : Fin 24 → Fin 24 → Bool) :
    threeHighTripleSupportSize
      (fun k => (threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor B)) ≤ 1608 := by
  have h (k : Fin 3) :
      ((threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor B)).length ≤ 536 := by
    calc
      _ ≤ (threeHighCanonicalTripleShapes k).length := List.length_filter_le _ _
      _ = 536 := threeHighCanonicalTripleShapes_length k
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  dsimp only [threeHighTripleSupportSize]
  omega

theorem threeHighCanonicalSupportRounds_stable (B : Fin 24 → Fin 24 → Bool) :
    threeHighTripleSupportPass B
      (threeHighTripleSupportRounds B
        (fun k => (threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor B)) 1608) =
      threeHighTripleSupportRounds B
        (fun k => (threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor B)) 1608 :=
  threeHighTripleSupportRounds_stable B 1608 _ (threeHighCanonicalSupportSize_le B)

/-- Further support passes cannot strengthen the search beyond this uniform bound. -/
theorem threeHighSupportedJointSearch_stable (B : Fin 24 → Fin 24 → Bool) (m : Nat) :
    threeHighSupportedJointSearch B (1608+m) = threeHighSupportedJointSearch B 1608 := by
  unfold threeHighSupportedJointSearch
  rw [threeHighTripleSupportRounds_add_stable B _ 1608 m (threeHighCanonicalSupportSize_le B)]

end Erdos85
#print axioms Erdos85.threeHighCanonicalSupportSize_le
#print axioms Erdos85.threeHighCanonicalSupportRounds_stable
#print axioms Erdos85.threeHighSupportedJointSearch_stable
