import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
import Proofs.Erdos85ThreeHighNativePairSearch

namespace Erdos85.VariedPilot.FullU54R20
open Erdos85
def U : Fin 15 → Fin 15 → Bool := threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 12 90))
def R : Fin 8 → Fin 8 → Bool :=
  threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 20)
end Erdos85.VariedPilot.FullU54R20
