import Proofs.Erdos85MuNegThreeZeroFiveOwnerCnf
import Proofs.Erdos85CnfCubeCover

/-!
# Correct h305 opposite-row cubes

For zero/zero shore mode and phase zero, row zero's opposite-sign DIMACS
variables are `2,4,6,8`.  Exact-three leaves four possible missing positions.
The `Std.Sat` unit identifiers below are their zero-based translations.
-/

namespace Erdos85

open Std Sat

def muNegThreeZeroFiveCorrectZZS0OppUnits (missing : Fin 4) :
    Array (Literal Nat) :=
  if missing.val = 0 then #[(1, false), (3, true), (5, true), (7, true)]
  else if missing.val = 1 then #[(1, true), (3, false), (5, true), (7, true)]
  else if missing.val = 2 then #[(1, true), (3, true), (5, false), (7, true)]
  else #[(1, true), (3, true), (5, true), (7, false)]

def muNegThreeZeroFiveCorrectZZS0OppCubeCnf (missing : Fin 4) : CNF Nat :=
  cnfWithUnits (muNegThreeZeroFiveOwnerSatCnf false false false)
    (muNegThreeZeroFiveCorrectZZS0OppUnits missing)

end Erdos85
