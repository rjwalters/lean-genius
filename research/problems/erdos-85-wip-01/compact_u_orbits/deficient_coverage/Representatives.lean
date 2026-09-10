import Deficient_3_3_0
namespace DeficientURepresentatives
open Erdos85
set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

def parameter (r : Fin 370) : ThreeBlockDeficientFirstRowParameters :=
  threeBlockDeficientCompactCode (DeficientUShard_3_3_0.repA r) (DeficientUShard_3_3_0.repB r) (DeficientUShard_3_3_0.repP r) (DeficientUShard_3_3_0.repD r)

theorem c4free (r : Fin 370) : encodedC4Free (DeficientUShard_3_3_0.representative r) = true := by
  decide +revert

private def parameterKey (p : ThreeBlockDeficientFirstRowParameters) : Nat :=
  (((p.1.1 0).val.toNat * 1024 + (p.1.1 1).val.toNat) * 120 +
    finFivePermutationRank p.1.2) * 5 + p.2.val

private theorem key_strictMono : StrictMono (fun r => parameterKey (parameter r)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  decide

theorem parameter_injective : Function.Injective parameter := by
  intro a b h
  exact key_strictMono.injective (congrArg parameterKey h)

end DeficientURepresentatives
#print axioms DeficientURepresentatives.c4free
#print axioms DeficientURepresentatives.parameter_injective
