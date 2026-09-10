import Proofs.Erdos85ThreeBlockMaskRelabeling

namespace Erdos85

/-- Diagonal relabelings that preserve the normalized first-row matching. -/
def threeBlockCanonicalStabilizer : Finset (Equiv.Perm (Fin 5)) :=
  Finset.univ.filter fun σ => ∀ i j,
    oneHighBranchBitAdj (129 : BitVec 10) i j =
      oneHighBranchBitAdj (129 : BitVec 10) (σ i) (σ j)

theorem mem_threeBlockCanonicalStabilizer (σ : Equiv.Perm (Fin 5)) :
    σ ∈ threeBlockCanonicalStabilizer ↔ ∀ i j,
      oneHighBranchBitAdj (129 : BitVec 10) i j =
        oneHighBranchBitAdj (129 : BitVec 10) (σ i) (σ j) := by
  simp only [threeBlockCanonicalStabilizer,Finset.mem_filter,Finset.mem_univ,true_and]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem threeBlockCanonicalStabilizer_card : threeBlockCanonicalStabilizer.card = 8 := by
  decide

end Erdos85
#print axioms Erdos85.mem_threeBlockCanonicalStabilizer
#print axioms Erdos85.threeBlockCanonicalStabilizer_card
