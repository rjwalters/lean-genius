import Proofs.Erdos85ThreeBlockCandidateDomains

namespace Erdos85

def finFiveMatchingMaskBits (i : Fin 15) : BitVec 10 :=
  ![129,257,513,34,66,514,20,68,260,24,40,136,528,288,192] i

set_option maxRecDepth 100000 in
theorem finFiveMatchingMaskBits_mem (i : Fin 15) :
    finFiveMatchingMaskBits i ∈ finFiveTwoEdgeMatchingMasks := by decide +revert

def finFiveMatchingMaskCode (i : Fin 15) : ThreeBlockMask :=
  ⟨finFiveMatchingMaskBits i,finFiveMatchingMaskBits_mem i⟩

theorem finFiveMatchingMaskCode_injective : Function.Injective finFiveMatchingMaskCode := by
  have hi : Function.Injective finFiveMatchingMaskBits := by decide
  intro i j h
  exact hi (congrArg Subtype.val h)

theorem finFiveMatchingMaskCode_surjective : Function.Surjective finFiveMatchingMaskCode := by
  classical
  by_contra h
  have hc := Fintype.card_lt_of_injective_not_surjective
    finFiveMatchingMaskCode finFiveMatchingMaskCode_injective h
  rw [Fintype.card_fin,threeBlockMask_card] at hc
  omega

end Erdos85
#print axioms Erdos85.finFiveMatchingMaskBits_mem
#print axioms Erdos85.finFiveMatchingMaskCode_injective
#print axioms Erdos85.finFiveMatchingMaskCode_surjective
