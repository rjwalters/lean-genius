import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCandidates
namespace FixedPairCoordinates
open Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def uRows : Fin 15 → BitVec 15 := ![1058,2113,4232,8452,16896,1281,8322,4164,16424,2064,8225,4610,2180,1096,272]
def rRows : Fin 8 → BitVec 8 := ![194,1,8,4,0,0,1,1]
def U : Fin 15 → Fin 15 → Bool := fun i j => (uRows i).getLsbD j.val
def R : Fin 8 → Fin 8 → Bool := fun i j => (rRows i).getLsbD j.val
theorem U_eq : U = threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15)) := by decide
theorem R_eq : R = threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14) := by decide
end FixedPairCoordinates
#print axioms FixedPairCoordinates.U_eq
#print axioms FixedPairCoordinates.R_eq
