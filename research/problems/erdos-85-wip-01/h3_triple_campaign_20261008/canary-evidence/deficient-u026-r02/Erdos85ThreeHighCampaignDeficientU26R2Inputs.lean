import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
import Proofs.Erdos85ThreeHighNativePairSearch
namespace Erdos85.TripleCampaign.DeficientU26R2
open Erdos85
def U : Fin 15 → Fin 15 → Bool := threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (threeBlockDeficientCompactCode 6 9 11 1))
def R : Fin 8 → Fin 8 → Bool :=
  threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 2)
end Erdos85.TripleCampaign.DeficientU26R2
