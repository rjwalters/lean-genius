import Proofs.Erdos85ThreeHighJointRelabeling
namespace FixedPairSymmetry
open Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def forward : Fin 16 → Fin 24 → Fin 24 := ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,22,21,23],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20,19,21,22,23],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20,19,22,21,23],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,17,19,20,21,22,23],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,17,19,20,22,21,23],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,17,20,19,21,22,23],![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,17,20,19,22,21,23],![2,3,0,1,4,12,13,10,11,14,7,8,5,6,9,15,16,17,18,19,20,21,22,23],![2,3,0,1,4,12,13,10,11,14,7,8,5,6,9,15,16,17,18,19,20,22,21,23],![2,3,0,1,4,12,13,10,11,14,7,8,5,6,9,15,16,17,18,20,19,21,22,23],![2,3,0,1,4,12,13,10,11,14,7,8,5,6,9,15,16,17,18,20,19,22,21,23],![2,3,0,1,4,12,13,10,11,14,7,8,5,6,9,15,16,18,17,19,20,21,22,23],![2,3,0,1,4,12,13,10,11,14,7,8,5,6,9,15,16,18,17,19,20,22,21,23],![2,3,0,1,4,12,13,10,11,14,7,8,5,6,9,15,16,18,17,20,19,21,22,23],![2,3,0,1,4,12,13,10,11,14,7,8,5,6,9,15,16,18,17,20,19,22,21,23]]
def blockForward : Fin 16 → Fin 3 → Fin 3 := ![![0,1,2],![0,1,2],![0,1,2],![0,1,2],![0,1,2],![0,1,2],![0,1,2],![0,1,2],![0,2,1],![0,2,1],![0,2,1],![0,2,1],![0,2,1],![0,2,1],![0,2,1],![0,2,1]]
theorem involutive_checked (g : Fin 16) : ∀ i, forward g (forward g i) = i := by decide +revert
theorem block_involutive_checked (g : Fin 16) : ∀ i, blockForward g (blockForward g i) = i := by decide +revert
def label (g : Fin 16) : Equiv.Perm (Fin 24) :=
  ⟨forward g, forward g, involutive_checked g, involutive_checked g⟩
def blockLabel (g : Fin 16) : Equiv.Perm (Fin 3) :=
  ⟨blockForward g, blockForward g, block_involutive_checked g, block_involutive_checked g⟩
theorem root_checked (g : Fin 16) : label g 23 = 23 := by decide +revert
theorem rows_checked (g : Fin 16) : ∀ k,
    (threeHighCanonicalRow k).image (label g) = threeHighCanonicalRow (blockLabel g k) := by decide +revert

theorem no_joint_transfer (A B : Fin 24 → Fin 24 → Bool) (g : Fin 16)
    (hAB : ∀ i j, A i j = B (label g i) (label g j))
    (hB : ¬ ThreeHighJointWitness B) : ¬ ThreeHighJointWitness A := by
  intro hA
  have h := hA.relabel A (label g) (blockLabel g) (root_checked g) (rows_checked g)
  have heq : (fun x y => A ((label g).symm x) ((label g).symm y)) = B := by
    funext x y
    rw [hAB]
    simp only [Equiv.apply_symm_apply]
  rw [heq] at h
  exact hB h
end FixedPairSymmetry
#print axioms FixedPairSymmetry.involutive_checked
#print axioms FixedPairSymmetry.block_involutive_checked
#print axioms FixedPairSymmetry.root_checked
#print axioms FixedPairSymmetry.rows_checked
#print axioms FixedPairSymmetry.no_joint_transfer
