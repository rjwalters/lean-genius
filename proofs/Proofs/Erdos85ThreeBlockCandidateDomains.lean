import Proofs.Erdos85OrderFortyNineThreeHighTripleTemplateAdmissible
import Mathlib.Data.Fintype.Perm

/-! Finite union parameter domains, filtered by the executable C4 condition.
The filters are definitions; this file does not evaluate their full contents. -/
namespace Erdos85

abbrev ThreeBlockMask := {bits : BitVec 10 // bits ∈ finFiveTwoEdgeMatchingMasks}
abbrev ThreeBlockFullParameters := (Fin 3 → ThreeBlockMask) × Equiv.Perm (Fin 5)
abbrev ThreeBlockDeficientParameters := ThreeBlockFullParameters × Fin 5

def threeBlockFullParameterAdj (p : ThreeBlockFullParameters) :
    (Fin 3 × Fin 5) → (Fin 3 × Fin 5) → Bool :=
  threeBlockMatchingAdj (fun k => (p.1 k).val) p.2

def threeBlockDeficientParameterAdj (p : ThreeBlockDeficientParameters) :
    (Fin 3 × Fin 5) → (Fin 3 × Fin 5) → Bool :=
  threeBlockDeficientMatchingAdj (fun k => (p.1.1 k).val) p.1.2 p.2

def threeBlockFullCandidates : Finset ThreeBlockFullParameters :=
  Finset.univ.filter fun p => encodedC4Free (threeBlockFullParameterAdj p)

def threeBlockDeficientCandidates : Finset ThreeBlockDeficientParameters :=
  Finset.univ.filter fun p => encodedC4Free (threeBlockDeficientParameterAdj p)

theorem threeBlockMask_card : Fintype.card ThreeBlockMask = 15 := by
  simpa using finFiveTwoEdgeMatchingMasks_card

theorem threeBlockFullParameters_card : Fintype.card ThreeBlockFullParameters = 405000 := by
  norm_num [ThreeBlockFullParameters, Fintype.card_perm, finFiveTwoEdgeMatchingMasks_card]

theorem threeBlockDeficientParameters_card : Fintype.card ThreeBlockDeficientParameters = 2025000 := by
  norm_num [ThreeBlockDeficientParameters, ThreeBlockFullParameters, Fintype.card_perm, finFiveTwoEdgeMatchingMasks_card]

theorem threeBlockFullCandidates_mem_iff (p : ThreeBlockFullParameters) :
    p ∈ threeBlockFullCandidates ↔ encodedC4Free (threeBlockFullParameterAdj p) = true := by
  simp [threeBlockFullCandidates]

theorem threeBlockDeficientCandidates_mem_iff (p : ThreeBlockDeficientParameters) :
    p ∈ threeBlockDeficientCandidates ↔ encodedC4Free (threeBlockDeficientParameterAdj p) = true := by
  simp [threeBlockDeficientCandidates]

end Erdos85
#print axioms Erdos85.threeBlockFullParameters_card
#print axioms Erdos85.threeBlockDeficientParameters_card
#print axioms Erdos85.threeBlockFullCandidates_mem_iff
#print axioms Erdos85.threeBlockDeficientCandidates_mem_iff
