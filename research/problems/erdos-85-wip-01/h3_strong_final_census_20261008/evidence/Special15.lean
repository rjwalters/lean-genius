import Proofs.Erdos85ThreeHighSelectedJointCertificate
import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCandidates
import Proofs.Erdos85ThreeHighExternalBlockFactorization
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable
namespace JointCanary
open Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def U := threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15))
def R := threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)
def rows : Fin 15 → BitVec 8 := ![2,16,64,32,132,4,8,128,16,96,64,32,2,8,144]
def cross : ThreeHighCross := fun i j => (rows i).getLsbD j.val

def adjRows : Fin 24 → BitVec 24 := ![66594,526401,2101384,1057028,4342272,132353,270466,4198468,540712,3147792,2105377,1053186,67716,263240,4718864,14745600,8425473,8650800,8527936,8405250,8391176,34308,49296,2064384]
def B : Fin 24 → Fin 24 → Bool := fun i j => (adjRows i).getLsbD j.val
 theorem B_eq : B = threeHighEmptyAdj U R cross := by decide

set_option maxHeartbeats 100000000
def D : Fin 3 → List (Finset (Fin 24)) := ![[{5,11,15},{5,11,17},{5,11,22},{5,12,17},{5,15,22},{5,20,22},{6,14,16},{6,14,20},{6,14,21},{6,15,21},{7,10,19},{7,10,20},{7,10,22},{7,20,22},{8,11,15},{8,11,18},{8,12,16},{8,12,18},{8,15,21},{8,18,21},{9,13,16},{9,13,19},{9,18,21},{9,19,21},{10,19,21},{10,20,22},{11,15,22},{11,18,22},{13,15,22},{14,18,21}],[{0,14,16},{0,14,18},{0,14,20},{0,18,22},{0,20,22},{1,11,15},{1,11,17},{1,11,22},{1,15,21},{1,15,22},{1,17,21},{1,19,21},{2,14,18},{2,14,21},{2,17,21},{2,18,21},{2,19,21},{3,13,15},{3,13,16},{3,13,22},{3,15,22},{3,20,22},{4,12,16},{4,12,17},{4,13,16},{10,19,21},{10,20,22},{11,15,22},{11,18,22},{13,15,22},{14,18,21}],[{0,7,20},{0,7,22},{0,9,16},{0,9,18},{0,18,22},{0,20,22},{1,6,15},{1,6,21},{1,15,21},{1,15,22},{1,17,21},{1,19,21},{2,5,17},{2,17,21},{2,18,21},{2,19,21},{3,8,15},{3,8,16},{3,15,22},{3,20,22},{4,6,16},{4,9,16},{5,15,22},{5,20,22},{6,15,21},{7,20,22},{8,15,21},{8,18,21},{9,18,21},{9,19,21}]]
theorem initial_cover_checked : (List.finRange 3).all (fun k =>
    (threeHighCanonicalTripleShapes k).all (fun S =>
      !threeHighTripleNoCommonNeighbor B S || decide (S ∈ D k))) = true := by decide
#print axioms initial_cover_checked
def E : Fin 3 → List (Finset (Fin 24)) := ![[{5,11,17},{5,11,22},{5,12,17},{5,20,22},{6,14,16},{6,14,20},{7,10,22},{7,20,22},{8,11,18},{8,12,16},{8,12,18},{8,15,21},{8,18,21},{9,13,19},{9,18,21},{9,19,21},{10,19,21},{11,18,22},{13,15,22},{14,18,21}],[{0,14,16},{0,14,18},{0,14,20},{0,18,22},{0,20,22},{1,11,17},{1,11,22},{1,15,22},{1,17,21},{1,19,21},{2,14,18},{2,17,21},{2,18,21},{2,19,21},{3,13,16},{3,13,22},{3,15,22},{3,20,22},{4,12,16},{4,12,17},{10,19,21},{11,15,22},{11,18,22},{13,15,22},{14,18,21}],[{0,7,20},{0,9,16},{0,9,18},{0,18,22},{0,20,22},{1,6,15},{1,6,21},{1,15,21},{1,17,21},{1,19,21},{2,5,17},{2,17,21},{2,18,21},{2,19,21},{3,8,16},{3,15,22},{3,20,22},{4,6,16},{4,9,16},{5,20,22},{6,15,21},{7,20,22},{8,15,21},{8,18,21},{9,18,21},{9,19,21}]]
theorem E_eq : E = threeHighTripleSupportPass B D := by decide

theorem no_cover_checked :
    threeHighListedJointSearch B E threeHighCanonicalResidual = false := by decide
#print axioms no_cover_checked

theorem admissible : cross ∈ threeHighCrossDomain U R := by
  apply (mem_threeHighCrossDomain_iff U R cross).mpr
  decide

theorem external_cap : encodedExternalBlockCap (threeHighEmptyAdj U R cross)
    threeHighCanonicalRow = true := by decide

theorem no_joint_literal : ¬ ThreeHighJointWitness B := by
  rintro ⟨F,hF,hblocks,hcompat,hcap⟩
  have hmem : ∀ i S, S ∈ F i → S ∈ D i := by
    intro i S hS
    have hi : S ∈ (threeHighCanonicalTripleShapes i).filter
        (threeHighTripleNoCommonNeighbor B) := by
      rw [threeHighCanonicalTripleShapes_filter]
      apply List.mem_filter.mpr
      refine ⟨?_, hblocks i S hS⟩
      rw [threeHighDirectTripleList_eq]
      exact (mem_threeHighEligibleTripleList B _ S).mpr
        (((mem_threeHighResolutionDomain B _ (F i)).mp (hF i)).1 hS)
    have hc := List.all_eq_true.mp
      (List.all_eq_true.mp initial_cover_checked i (List.mem_finRange i)) S (List.mem_filter.mp hi).1
    simpa only [(List.mem_filter.mp hi).2, Bool.not_true, Bool.false_or,
      decide_eq_true_eq] using hc
  have hpass := threeHighTripleSupportPass_preserves B D F hmem
    (fun i j _ => hcompat i j)
  rw [← E_eq] at hpass
  have ht := threeHighListedJointSearch_of_families B E threeHighCanonicalResidual F
    hF hpass (fun i j _ => hcompat i j) hcap
  rw [no_cover_checked] at ht
  contradiction

theorem no_joint : ¬ ThreeHighJointWitness (threeHighEmptyAdj U R cross) := by
  rw [← B_eq]
  exact no_joint_literal
end JointCanary
#print axioms JointCanary.B_eq
#print axioms JointCanary.admissible
#print axioms JointCanary.external_cap
#print axioms JointCanary.no_joint_literal
#print axioms JointCanary.no_joint

