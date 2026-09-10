import Full_3_3
namespace FullURepresentatives
open Erdos85
set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

def parameter (r : Fin 55) : ThreeBlockFirstRowParameters :=
  threeBlockCompactCode (FullUShard_3_3.repA r) (FullUShard_3_3.repB r) (FullUShard_3_3.repP r)

theorem c4free (r : Fin 55) : encodedC4Free (FullUShard_3_3.representative r) = true := by
  decide +revert

theorem parameter_injective : Function.Injective parameter := by
  decide

end FullURepresentatives
#print axioms FullURepresentatives.c4free
#print axioms FullURepresentatives.parameter_injective
