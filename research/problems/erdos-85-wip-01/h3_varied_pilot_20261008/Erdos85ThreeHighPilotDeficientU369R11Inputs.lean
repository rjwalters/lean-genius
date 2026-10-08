import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
import Proofs.Erdos85ThreeHighNativePairSearch

namespace Erdos85.VariedPilot.DeficientU369R11
open Erdos85
def U : Fin 15 → Fin 15 → Bool := threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (threeBlockDeficientCompactCode 9 12 92 2))
def R : Fin 8 → Fin 8 → Bool :=
  threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 11)
end Erdos85.VariedPilot.DeficientU369R11
