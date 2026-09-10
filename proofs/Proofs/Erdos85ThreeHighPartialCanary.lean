import Proofs.Erdos85ThreeHighSelectedSeparatedCertificate
import Proofs.Erdos85ThreeHighJointSubgraph
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCandidates

namespace Erdos85.PartialCanary
open Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

def U := threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15))
def R := threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)
def rows : Fin 15 → BitVec 8 := ![2,4,16,64,160,0,128,2,8,80,16,4,0,64,136]
def cross : ThreeHighCross := fun i j => (rows i).getLsbD j.val

def adjRows : Fin 24 → BitVec 24 := ![66594,133185,528520,2105604,5259776,1281,4202626,69700,278568,2623504,532513,135682,2180,2098248,4456720,14745600,8421505,8652802,8536320,8390148,8388624,41480,49232,2064384]
def B : Fin 24 → Fin 24 → Bool := fun i j => (adjRows i).getLsbD j.val

theorem B_eq : B = threeHighEmptyAdj U R cross := by decide

def D : Fin 3 → List (Finset (Fin 24)) := ![[{5,11,15},{5,11,20},{5,11,22},{5,12,15},{5,12,20},{5,12,21},{5,12,22},{5,15,21},{5,15,22},{5,17,21},{5,17,22},{5,20,21},{6,13,18},{6,13,20},{6,19,22},{7,10,17},{7,10,18},{7,10,20},{7,14,16},{7,14,21},{7,17,21},{7,18,21},{7,20,21},{8,11,15},{8,11,16},{8,11,20},{8,12,15},{8,12,20},{9,11,16},{9,18,21},{10,15,22},{10,17,22},{10,19,22},{11,15,22},{12,15,21},{12,15,22},{12,18,21},{12,20,21}],[{0,12,18},{0,12,20},{0,12,21},{0,12,22},{0,14,16},{0,14,21},{0,18,21},{0,20,21},{1,14,19},{1,14,21},{1,15,21},{1,20,21},{2,14,19},{2,15,22},{2,17,22},{2,19,22},{3,11,16},{3,11,20},{3,11,22},{3,17,22},{4,10,17},{4,10,20},{4,12,20},{4,13,16},{4,13,17},{4,13,20},{10,15,22},{10,17,22},{10,19,22},{11,15,22},{12,15,21},{12,15,22},{12,18,21},{12,20,21}],[{0,9,16},{0,9,18},{0,9,21},{0,18,21},{0,20,21},{1,6,19},{1,6,20},{1,8,15},{1,8,19},{1,8,20},{1,15,21},{1,20,21},{2,5,15},{2,5,17},{2,5,20},{2,5,22},{2,15,22},{2,17,22},{2,19,22},{3,8,16},{3,8,20},{3,17,22},{4,5,17},{4,5,20},{4,7,16},{4,7,17},{4,7,20},{4,9,16},{5,15,21},{5,15,22},{5,17,21},{5,17,22},{5,20,21},{6,19,22},{7,17,21},{7,18,21},{7,20,21},{9,18,21}]]
def X : Finset (Fin 24) := {9,11,12,13,14,17,19}

theorem initial_cover_checked : threeHighInitialTripleCoverChecked B D = true := by decide

theorem separated_checked : listedSeparatedCap (threeHighTripleSupportPass B D 0) X = true := by decide

theorem no_joint : ¬ ThreeHighJointWitness B :=
  threeHighSelectedSeparatedCertificate_no_joint B D initial_cover_checked 0 X
    (by decide) (by decide) separated_checked

theorem no_joint_extension (C : Fin 24 → Fin 24 → Bool)
    (hsub : EncodedSubgraph B C) : ¬ ThreeHighJointWitness C := by
  intro hC
  exact no_joint (hC.of_subgraph B C hsub)

theorem no_cross_extension (c : ThreeHighCross)
    (hsub : ∀ i j, cross i j = true → c i j = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj U R c) := by
  apply no_joint_extension
  rw [B_eq]
  exact threeHighEmptyAdj_subgraph U R cross c hsub

end Erdos85.PartialCanary
#print axioms Erdos85.PartialCanary.B_eq
#print axioms Erdos85.PartialCanary.initial_cover_checked
#print axioms Erdos85.PartialCanary.separated_checked
#print axioms Erdos85.PartialCanary.no_joint
#print axioms Erdos85.PartialCanary.no_joint_extension
#print axioms Erdos85.PartialCanary.no_cross_extension
