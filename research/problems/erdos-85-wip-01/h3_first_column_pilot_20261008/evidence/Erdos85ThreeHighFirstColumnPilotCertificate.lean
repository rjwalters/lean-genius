import Proofs.Erdos85ThreeHighFirstColumnSearch
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable

/-! One first-column branch of the existing U1/R15 pilot. A rejection here
does not exclude the whole pair: the other fourteen columns remain. -/

namespace Erdos85.FirstColumnPilot

def U : Fin 15 → Fin 15 → Bool :=
  threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15))

def R : Fin 8 → Fin 8 → Bool :=
  threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 15)

def S : Finset (Fin 15) := {0}

set_option maxRecDepth 100000 in
theorem rejected : threeHighNativeFirstColumnSearch U R S = false := by
  native_decide

end Erdos85.FirstColumnPilot

#print axioms Erdos85.FirstColumnPilot.rejected
