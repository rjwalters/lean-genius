import Proofs.Erdos85ThreeHighRSwapJointSearch
import Proofs.Erdos85ThreeHighRSwapTable
namespace RSwapCanary
open Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def rowTable : Fin 8 → Fin 15 → BitVec 8 := ![![2,4,16,64,160,32,128,2,8,80,16,4,32,64,136],![2,4,16,128,96,32,64,2,8,144,16,4,32,128,72],![2,4,64,16,160,32,128,2,8,80,64,4,32,16,136],![2,4,128,16,96,32,64,2,8,144,128,4,32,16,72],![2,4,32,64,144,16,128,2,8,96,32,4,16,64,136],![2,4,32,128,80,16,64,2,8,160,32,4,16,128,72],![2,4,64,32,144,16,128,2,8,96,64,4,16,32,136],![2,4,128,32,80,16,64,2,8,160,128,4,16,32,72]]
def cross (k : Fin 8) : ThreeHighCross := fun i j => (rowTable k i).getLsbD j.val

theorem valid : threeHighRSwapPairsValid
    (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14))
    (threeHighSecondarySwapPairs 14) = true := by decide

theorem ordered (k : Fin 8) :
    threeHighRSwapOrdered (threeHighSecondarySwapPairs 14) threeHighColumnScore (cross k) =
      decide (k = 0 ∨ k = 6) := by
  decide +revert
end RSwapCanary
#print axioms RSwapCanary.valid
#print axioms RSwapCanary.ordered
