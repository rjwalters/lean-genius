import Proofs.Erdos85ThreeBlockSharedEdge
import Proofs.Erdos85ThreeBlockCompactCodes

namespace Erdos85

def threeBlockDisjointMaskCodes : Finset (Fin 15) :=
  Finset.univ.filter fun a => ∀ i j : Fin 5,
    oneHighBranchBitAdj 129 i j = true →
      oneHighBranchBitAdj (finFiveMatchingMaskCode a).val j i = false

theorem threeBlockDisjointMaskCodes_eq :
    threeBlockDisjointMaskCodes = {3,4,5,6,7,8,9,10,12,13} := by decide

theorem threeBlockDisjointMaskCodes_card : threeBlockDisjointMaskCodes.card = 10 := by
  decide

def threeBlockDisjointMaskPairs : Finset (Fin 15 × Fin 15) :=
  threeBlockDisjointMaskCodes ×ˢ threeBlockDisjointMaskCodes

theorem threeBlockDisjointMaskPairs_card : threeBlockDisjointMaskPairs.card = 100 := by
  simp [threeBlockDisjointMaskPairs,Finset.card_product,threeBlockDisjointMaskCodes_card]

theorem threeBlockCompactCode_disjoint_masks (a b : Fin 15) (p : Fin 120)
    (hf : encodedC4Free (threeBlockFullParameterAdj
      (threeBlockFirstRowEmbed (threeBlockCompactCode a b p))) = true) :
    (a,b) ∈ threeBlockDisjointMaskPairs := by
  have one (k : Fin 2) : (![a,b] k) ∈ threeBlockDisjointMaskCodes := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro i j h0
    cases h1 : oneHighBranchBitAdj (finFiveMatchingMaskCode (![a,b] k)).val j i
    · rfl
    · apply False.elim
      apply threeBlockMatchingAdj_shared_edge _ _ hf k.succ (Fin.succ_ne_zero k) i j
      · simpa [threeBlockFirstRowEmbed,threeBlockCompactCode,threeBlockCanonicalMask] using h0
      · fin_cases k <;> exact h1
  exact Finset.mem_product.mpr ⟨one 0,one 1⟩

theorem threeBlockDeficientCompactCode_disjoint_masks (a b : Fin 15) (p : Fin 120) (d : Fin 5)
    (hf : encodedC4Free (threeBlockDeficientParameterAdj
      (threeBlockDeficientFirstRowEmbed (threeBlockDeficientCompactCode a b p d))) = true) :
    (a,b) ∈ threeBlockDisjointMaskPairs := by
  have one (k : Fin 2) : (![a,b] k) ∈ threeBlockDisjointMaskCodes := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro i j h0
    cases h1 : oneHighBranchBitAdj (finFiveMatchingMaskCode (![a,b] k)).val j i
    · rfl
    · apply False.elim
      apply threeBlockDeficientMatchingAdj_shared_edge _ _ _ hf k.succ (Fin.succ_ne_zero k) i j
      · simpa [threeBlockDeficientFirstRowEmbed,threeBlockDeficientCompactCode,
          threeBlockFirstRowEmbed,threeBlockCompactCode,threeBlockCanonicalMask] using h0
      · fin_cases k <;> exact h1
  exact Finset.mem_product.mpr ⟨one 0,one 1⟩

end Erdos85
#print axioms Erdos85.threeBlockDisjointMaskCodes_eq
#print axioms Erdos85.threeBlockDisjointMaskCodes_card
#print axioms Erdos85.threeBlockDisjointMaskPairs_card
#print axioms Erdos85.threeBlockCompactCode_disjoint_masks
#print axioms Erdos85.threeBlockDeficientCompactCode_disjoint_masks
