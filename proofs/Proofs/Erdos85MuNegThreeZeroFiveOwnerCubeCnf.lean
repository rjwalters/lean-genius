import Proofs.Erdos85MuNegThreeZeroFiveOwnerCnf
import Proofs.Erdos85CnfCubeCover

/-!
# Four-cube reduction for the h305 opposite-sign row

In phase zero, row zero's opposite-sign defect variables are `2,4,6,8`.
The h305 ledger forces exactly three of them true, so four cubes exhaust the
row.  Fixing only these four literals collapses the otherwise very large
owner proof to unit propagation.
-/

namespace Erdos85

open Std Sat

def muNegThreeZeroFiveZZS0OppUnits (missing : Fin 4) :
    Array (Literal Nat) :=
  if missing.val = 0 then #[(1, false), (3, true), (5, true), (7, true)]
  else if missing.val = 1 then #[(1, true), (3, false), (5, true), (7, true)]
  else if missing.val = 2 then #[(1, true), (3, true), (5, false), (7, true)]
  else #[(1, true), (3, true), (5, true), (7, false)]

def muNegThreeZeroFiveZZS0OppCubeCnf (missing : Fin 4) : CNF Nat :=
  cnfWithUnits (muNegThreeZeroFiveOwnerSatCnf false false false)
    (muNegThreeZeroFiveZZS0OppUnits missing)

end Erdos85
