import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
import Proofs.Erdos85ThreeHighNativePairSearch
namespace Erdos85.TripleCampaign.FullU1R16
open Erdos85
def U : Fin 15 → Fin 15 → Bool := threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15))
def R : Fin 8 → Fin 8 → Bool :=
  threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 16)
end Erdos85.TripleCampaign.FullU1R16
