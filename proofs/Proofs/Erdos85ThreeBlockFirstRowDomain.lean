import Proofs.Erdos85ThreeBlockFirstRowNormalization

namespace Erdos85

abbrev ThreeBlockFirstRowParameters := (Fin 2 → ThreeBlockMask) × Equiv.Perm (Fin 5)
abbrev ThreeBlockDeficientFirstRowParameters := ThreeBlockFirstRowParameters × Fin 5

def threeBlockFirstRowEmbed (p : ThreeBlockFirstRowParameters) : ThreeBlockFullParameters :=
  (Fin.cases threeBlockCanonicalMask p.1,p.2)

def threeBlockDeficientFirstRowEmbed (p : ThreeBlockDeficientFirstRowParameters) :
    ThreeBlockDeficientParameters := (threeBlockFirstRowEmbed p.1,p.2)

theorem threeBlockFirstRowParameters_card : Fintype.card ThreeBlockFirstRowParameters = 27000 := by
  norm_num [ThreeBlockFirstRowParameters,Fintype.card_perm,finFiveTwoEdgeMatchingMasks_card]

theorem threeBlockDeficientFirstRowParameters_card :
    Fintype.card ThreeBlockDeficientFirstRowParameters = 135000 := by
  norm_num [ThreeBlockDeficientFirstRowParameters,ThreeBlockFirstRowParameters,
    Fintype.card_perm,finFiveTwoEdgeMatchingMasks_card]

theorem threeBlockFirstRowEmbed_cover (p : ThreeBlockFullParameters)
    (hp : p.1 0 = threeBlockCanonicalMask) :
    ∃ q : ThreeBlockFirstRowParameters, threeBlockFirstRowEmbed q = p := by
  refine ⟨(fun i => p.1 i.succ,p.2),?_⟩
  apply Prod.ext
  · funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · exact hp.symm
    · rfl
  · rfl

theorem threeBlockDeficientFirstRowEmbed_cover (p : ThreeBlockDeficientParameters)
    (hp : p.1.1 0 = threeBlockCanonicalMask) :
    ∃ q : ThreeBlockDeficientFirstRowParameters, threeBlockDeficientFirstRowEmbed q = p := by
  obtain ⟨q,hq⟩ := threeBlockFirstRowEmbed_cover p.1 hp
  exact ⟨(q,p.2),by simp only [threeBlockDeficientFirstRowEmbed,hq]⟩

end Erdos85
#print axioms Erdos85.threeBlockFirstRowParameters_card
#print axioms Erdos85.threeBlockDeficientFirstRowParameters_card
#print axioms Erdos85.threeBlockFirstRowEmbed_cover
#print axioms Erdos85.threeBlockDeficientFirstRowEmbed_cover
