import Proofs.Erdos85ThreeHighNativePairSearch
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable

/-! Conditional consumer elaboration probe; does not evaluate the finite search. -/

namespace Erdos85

namespace NativeTerminalConsumerProbe

def U : Fin 15 → Fin 15 → Bool :=
  threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15))

def R : Fin 8 → Fin 8 → Bool :=
  threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 15)

theorem no_joint (hreject : threeHighNativePairSearch U R = false)
    (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj U R cross) :=
  threeHighNativePairSearch_no_joint U R hreject cross hc he

end NativeTerminalConsumerProbe

end Erdos85

#print axioms Erdos85.NativeTerminalConsumerProbe.no_joint
