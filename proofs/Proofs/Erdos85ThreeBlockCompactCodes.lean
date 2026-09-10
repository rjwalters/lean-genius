import Proofs.Erdos85FinFivePermutationCodes
import Proofs.Erdos85FinFiveMatchingMaskCodes
import Proofs.Erdos85ThreeBlockFirstRowDomain

namespace Erdos85

def threeBlockCompactCode (a b : Fin 15) (p : Fin 120) : ThreeBlockFirstRowParameters :=
  (![finFiveMatchingMaskCode a,finFiveMatchingMaskCode b],finFivePermutationCode p)

def threeBlockDeficientCompactCode (a b : Fin 15) (p : Fin 120) (d : Fin 5) :
    ThreeBlockDeficientFirstRowParameters := (threeBlockCompactCode a b p,d)

theorem threeBlockCompactCode_covers (p : ThreeBlockFirstRowParameters) :
    ∃ a b i, threeBlockCompactCode a b i = p := by
  obtain ⟨a,ha⟩ := finFiveMatchingMaskCode_surjective (p.1 0)
  obtain ⟨b,hb⟩ := finFiveMatchingMaskCode_surjective (p.1 1)
  obtain ⟨i,hi⟩ := finFivePermutationCode_surjective p.2
  refine ⟨a,b,i,?_⟩
  apply Prod.ext
  · funext k
    fin_cases k
    · exact ha
    · exact hb
  · exact hi

theorem threeBlockDeficientCompactCode_covers (p : ThreeBlockDeficientFirstRowParameters) :
    ∃ a b i d, threeBlockDeficientCompactCode a b i d = p := by
  obtain ⟨a,b,i,hi⟩ := threeBlockCompactCode_covers p.1
  exact ⟨a,b,i,p.2,by simp only [threeBlockDeficientCompactCode,hi]⟩

end Erdos85
#print axioms Erdos85.threeBlockCompactCode_covers
#print axioms Erdos85.threeBlockDeficientCompactCode_covers
