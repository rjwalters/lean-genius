import Proofs.Erdos85ThreeHighSelectedCoverCertificate
import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCandidates
import Proofs.Erdos85ThreeHighExternalBlockFactorization
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
namespace ExactCoverCanary
open Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def U := threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15))
def R := threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)
def rows : Fin 15 → BitVec 8 := ![4,2,64,16,160,32,128,4,8,80,64,2,32,16,136]
def cross : ThreeHighCross := fun i j => (rows i).getLsbD j.val

def adjRows : Fin 24 → BitVec 24 := ![132130,67649,2101384,532740,5259776,1049857,4202626,135236,278568,2623504,2105377,70146,1050756,525384,4456720,14745600,8423426,8650881,8536320,8397320,8392752,34308,49232,2064384]
def B : Fin 24 → Fin 24 → Bool := fun i j => (adjRows i).getLsbD j.val
 theorem B_eq : B = threeHighEmptyAdj U R cross := by decide

set_option maxHeartbeats 100000000
def D : Fin 3 → List (Finset (Fin 24)) := ![[{5,11,22},{5,15,22},{5,19,22},{6,13,18},{6,13,20},{6,18,21},{6,20,21},{7,10,16},{7,14,16},{7,14,19},{8,12,15},{8,15,21},{9,11,17},{9,11,18},{9,17,21},{9,18,21},{10,18,21},{11,17,22},{12,15,22},{12,19,22}],[{0,12,15},{0,12,19},{0,12,22},{0,14,19},{0,15,22},{0,17,22},{0,19,22},{1,14,19},{1,14,21},{1,18,21},{1,20,21},{2,14,16},{2,14,21},{2,18,21},{3,11,17},{3,11,22},{3,15,22},{3,17,22},{4,10,16},{4,13,16},{4,13,17},{4,13,20},{10,18,21},{11,17,22},{12,15,22},{12,19,22}],[{0,9,17},{0,9,19},{0,15,22},{0,17,22},{0,19,22},{1,6,18},{1,6,20},{1,6,21},{1,8,21},{1,18,21},{1,20,21},{2,5,16},{2,5,22},{2,18,21},{3,8,15},{3,8,16},{3,15,22},{3,17,22},{4,7,16},{4,7,17},{4,9,17},{5,15,22},{5,19,22},{6,18,21},{6,20,21},{8,15,21},{9,17,21},{9,18,21}]]
theorem initial_cover_checked : (List.finRange 3).all (fun k =>
    (threeHighCanonicalTripleShapes k).all (fun S =>
      !threeHighTripleNoCommonNeighbor B S || decide (S ∈ D k))) = true := by decide
#print axioms initial_cover_checked
theorem no_cover_checked :
    finitePivotCoverSearch (D 1) 6 (threeHighCanonicalResidual 1) = false := by decide
#print axioms no_cover_checked

theorem admissible : cross ∈ threeHighCrossDomain U R := by
  apply (mem_threeHighCrossDomain_iff U R cross).mpr
  decide

theorem external_cap : encodedExternalBlockCap (threeHighEmptyAdj U R cross)
    threeHighCanonicalRow = true := by decide

theorem no_joint_literal : ¬ ThreeHighJointWitness B := by
  exact threeHighSelectedCoverCertificate_no_joint B D initial_cover_checked 1 no_cover_checked

theorem no_joint : ¬ ThreeHighJointWitness (threeHighEmptyAdj U R cross) := by
  rw [← B_eq]
  exact no_joint_literal
end ExactCoverCanary
#print axioms ExactCoverCanary.B_eq
#print axioms ExactCoverCanary.admissible
#print axioms ExactCoverCanary.external_cap
#print axioms ExactCoverCanary.no_joint_literal
#print axioms ExactCoverCanary.no_joint

