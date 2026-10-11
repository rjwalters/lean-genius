import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
import Proofs.Erdos85ThreeHighNativePairSearch

namespace Erdos85.VariedPilot.FullU3R3
open Erdos85
def U : Fin 15 → Fin 15 → Bool := threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 9 5))
def R : Fin 8 → Fin 8 → Bool :=
  threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 3)
end Erdos85.VariedPilot.FullU3R3
