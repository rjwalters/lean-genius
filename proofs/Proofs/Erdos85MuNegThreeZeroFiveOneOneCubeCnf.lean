import Proofs.Erdos85MuNegThreeZeroFiveOwnerCnf
import Proofs.Erdos85CnfCubeCover

/-!
# Correct h305 one/one-shore opposite-row cubes

For mixed shore mode, exact-three on row zero's opposite-sign variables leaves
four possible missing positions.  Phase zero uses DIMACS variables `2,4,6,8`;
phase one uses `1,3,5,7`.
-/

namespace Erdos85

open Std Sat

def muNegThreeZeroFiveCorrectOneOneS0OppUnits (missing : Fin 4) :
    Array (Literal Nat) :=
  if missing.val = 0 then #[(1, false), (3, true), (5, true), (7, true)]
  else if missing.val = 1 then #[(1, true), (3, false), (5, true), (7, true)]
  else if missing.val = 2 then #[(1, true), (3, true), (5, false), (7, true)]
  else #[(1, true), (3, true), (5, true), (7, false)]

def muNegThreeZeroFiveCorrectOneOneS0OppCubeCnf (missing : Fin 4) : CNF Nat :=
  cnfWithUnits (muNegThreeZeroFiveOwnerSatCnf true true false)
    (muNegThreeZeroFiveCorrectOneOneS0OppUnits missing)

def muNegThreeZeroFiveCorrectOneOneS1OppUnits (missing : Fin 4) :
    Array (Literal Nat) :=
  if missing.val = 0 then #[(0, false), (2, true), (4, true), (6, true)]
  else if missing.val = 1 then #[(0, true), (2, false), (4, true), (6, true)]
  else if missing.val = 2 then #[(0, true), (2, true), (4, false), (6, true)]
  else #[(0, true), (2, true), (4, true), (6, false)]

def muNegThreeZeroFiveCorrectOneOneS1OppCubeCnf (missing : Fin 4) : CNF Nat :=
  cnfWithUnits (muNegThreeZeroFiveOwnerSatCnf true true true)
    (muNegThreeZeroFiveCorrectOneOneS1OppUnits missing)

end Erdos85

