import Proofs.Erdos85ThreeHighSelectedSeparatedCertificate
import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCandidates
import Proofs.Erdos85ThreeHighExternalBlockFactorization
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
namespace SecondColumnCanary
open Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def U := threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15))
def R := threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)
def rows : Fin 15 → BitVec 8 := ![2,4,64,16,160,32,128,2,8,80,64,4,32,16,136]
def cross : ThreeHighCross := fun i j => (rows i).getLsbD j.val

def adjRows : Fin 24 → BitVec 24 := ![66594,133185,2101384,532740,5259776,1049857,4202626,69700,278568,2623504,2105377,135682,1050756,525384,4456720,14745600,8421505,8652802,8536320,8397320,8392752,34308,49232,2064384]
def B : Fin 24 → Fin 24 → Bool := fun i j => (adjRows i).getLsbD j.val
 theorem B_eq : B = threeHighEmptyAdj U R cross := by decide

set_option maxHeartbeats 100000000
def D : Fin 3 → List (Finset (Fin 24)) := ![[{5,11,15},{5,11,22},{5,15,22},{5,17,22},{5,19,22},{6,13,18},{6,13,20},{6,18,21},{6,20,21},{7,10,17},{7,10,18},{7,14,16},{7,14,19},{8,11,15},{8,11,16},{8,12,15},{8,15,21},{9,11,16},{9,18,21},{10,17,21},{10,17,22},{10,18,21},{11,15,22},{12,15,22},{12,19,22}],[{0,12,18},{0,12,19},{0,12,22},{0,14,16},{0,14,19},{0,19,22},{1,14,19},{1,14,21},{1,15,21},{1,20,21},{2,14,21},{2,17,21},{2,17,22},{2,18,21},{3,11,15},{3,11,16},{3,11,22},{3,15,22},{3,17,22},{4,10,17},{4,13,16},{4,13,17},{4,13,20},{10,17,21},{10,17,22},{10,18,21},{11,15,22},{12,15,22},{12,19,22}],[{0,9,16},{0,9,18},{0,9,19},{0,19,22},{1,6,20},{1,6,21},{1,8,15},{1,8,21},{1,15,21},{1,20,21},{2,5,17},{2,5,22},{2,17,21},{2,17,22},{2,18,21},{3,8,15},{3,8,16},{3,15,22},{3,17,22},{4,7,16},{4,7,17},{4,9,16},{5,15,22},{5,17,22},{5,19,22},{6,18,21},{6,20,21},{8,15,21},{9,18,21}]]
def X : Finset (Fin 24) := {0,1,2,10,11,13,15}
theorem initial_cover_checked : (List.finRange 3).all (fun k =>
    (threeHighCanonicalTripleShapes k).all (fun S =>
      !threeHighTripleNoCommonNeighbor B S || decide (S ∈ D k))) = true := by decide
#print axioms initial_cover_checked
theorem separated_checked :
    listedSeparatedCap (threeHighTripleSupportPass B D 1) X = true := by decide
#print axioms separated_checked

theorem admissible : cross ∈ threeHighCrossDomain U R := by
  apply (mem_threeHighCrossDomain_iff U R cross).mpr
  decide

theorem external_cap : encodedExternalBlockCap (threeHighEmptyAdj U R cross)
    threeHighCanonicalRow = true := by decide

theorem no_joint_literal : ¬ ThreeHighJointWitness B := by
  exact threeHighSelectedSeparatedCertificate_no_joint B D initial_cover_checked 1 X
    (by decide) (by decide) separated_checked

theorem no_joint : ¬ ThreeHighJointWitness (threeHighEmptyAdj U R cross) := by
  rw [← B_eq]
  exact no_joint_literal
end SecondColumnCanary
#print axioms SecondColumnCanary.B_eq
#print axioms SecondColumnCanary.admissible
#print axioms SecondColumnCanary.external_cap
#print axioms SecondColumnCanary.no_joint_literal
#print axioms SecondColumnCanary.no_joint

