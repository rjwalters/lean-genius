import SubsetPair20_3Inputs
import Proofs.Erdos85ThreeHighColumnSubsetCapacity
namespace SubsetPair20_3
open Erdos85
attribute [local irreducible] threeHighCrossDomain
theorem checked : threeHighColumnSubsetCapacityCheck U domains S caps = true := by
  simp only [threeHighColumnSubsetCapacityCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨deficit, List.all_eq_true.mpr (fun j _ => caps_checked j)⟩
theorem impossible_literal (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) : False :=
  threeHighWitnessedColumnSubsetCapacity_impossible U R domains reasons S caps domains_checked checked cross hc he
theorem impossible (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 16))) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 3)))
    (he : encodedExternalBlockCap (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 16))) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 3)) cross) threeHighCanonicalRow = true) : False := by
  rw [← U_eq, ← R_eq] at hc he
  exact impossible_literal cross hc he

theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 16))) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 3)))
    (he : encodedExternalBlockCap (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 16))) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 3)) cross) threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 16))) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 3)) cross) := (impossible cross hc he).elim
end SubsetPair20_3
#print axioms SubsetPair20_3.checked
#print axioms SubsetPair20_3.impossible_literal
#print axioms SubsetPair20_3.impossible
#print axioms SubsetPair20_3.no_joint
