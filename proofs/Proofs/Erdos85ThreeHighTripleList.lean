import Proofs.Erdos85ThreeHighResolutionDomain
import Proofs.Erdos85FiniteExactCoverSearch

namespace Erdos85

def threeHighTripleList : List (Finset (Fin 24)) :=
  ((List.finRange 24).sublistsLen 3).map List.toFinset

def threeHighEligibleTripleList (B : Fin 24 → Fin 24 → Bool) (R : Finset (Fin 24)) :
    List (Finset (Fin 24)) :=
  threeHighTripleList.filter fun S => S ∈ threeHighEligibleTriples B R

theorem threeHighTripleList_length : threeHighTripleList.length = 2024 := by
  simp [threeHighTripleList, List.length_sublistsLen]
  decide

theorem threeHighTripleList_complete (S : Finset (Fin 24)) (hS : S.card = 3) :
    S ∈ threeHighTripleList := by
  let l := (List.finRange 24).filter fun j => j ∈ S
  have he : l.toFinset = S := by
    ext j
    simp [l]
  have hn : l.Nodup := (List.nodup_finRange 24).filter _
  have hl : l.length = 3 := by
    rw [← List.toFinset_card_of_nodup hn, he, hS]
  apply List.mem_map.mpr
  exact ⟨l, List.mem_sublistsLen.mpr ⟨List.filter_sublist, hl⟩, he⟩

theorem mem_threeHighEligibleTripleList (B : Fin 24 → Fin 24 → Bool)
    (R S : Finset (Fin 24)) :
    S ∈ threeHighEligibleTripleList B R ↔ S ∈ threeHighEligibleTriples B R := by
  constructor
  · intro h
    exact of_decide_eq_true (List.mem_filter.mp h).2
  · intro h
    apply List.mem_filter.mpr
    exact ⟨threeHighTripleList_complete S ((mem_threeHighEligibleTriples B R S).mp h).2.1,
      by simpa using h⟩

def threeHighResolutionSearch (B : Fin 24 → Fin 24 → Bool) (R : Finset (Fin 24)) : Bool :=
  finiteExactCoverSearch (threeHighEligibleTripleList B R) 6 R

theorem threeHighResolutionSearch_of_mem (B : Fin 24 → Fin 24 → Bool)
    (R : Finset (Fin 24)) (F : Finset (Finset (Fin 24)))
    (hF : F ∈ threeHighResolutionDomain B R) : threeHighResolutionSearch B R = true := by
  obtain ⟨hsub,hcard,hdis,hcover⟩ := (mem_threeHighResolutionDomain B R F).mp hF
  exact finiteExactCoverSearch_of_family _ 6 R F
    (fun S hS => (mem_threeHighEligibleTripleList B R S).mpr (hsub hS)) hcard hdis hcover

end Erdos85
#print axioms Erdos85.threeHighTripleList_length
#print axioms Erdos85.threeHighTripleList_complete
#print axioms Erdos85.mem_threeHighEligibleTripleList
#print axioms Erdos85.threeHighResolutionSearch_of_mem
