import Proofs.Erdos85ResolutionSeparatedBound
import Proofs.Erdos85GreedySeparatedSet
import Proofs.Erdos85ThreeHighResolutionDomain

namespace Erdos85

def threeHighGreedySeparated (D : List (Finset (Fin 24))) (R : Finset (Fin 24)) :
    Finset (Fin 24) :=
  greedySeparatedSet D ((List.finRange 24).filter (fun x => decide (x ∈ R))) ∅

def threeHighSeparatedGate (D : List (Finset (Fin 24))) (R : Finset (Fin 24)) : Bool :=
  decide ((threeHighGreedySeparated D R).card ≤ 6)

theorem threeHighSeparatedGate_of_resolution
    (B : Fin 24 → Fin 24 → Bool) (D : List (Finset (Fin 24)))
    (R : Finset (Fin 24)) (F : Finset (Finset (Fin 24)))
    (hF : F ∈ threeHighResolutionDomain B R) (hD : ∀ S ∈ F, S ∈ D) :
    threeHighSeparatedGate D R = true := by
  have hf := (mem_threeHighResolutionDomain B R F).mp hF
  have hs : threeHighGreedySeparated D R ⊆ R := by
    apply greedySeparatedSet_subset D _ ∅ R (Finset.empty_subset _)
    intro x hx
    exact of_decide_eq_true (List.mem_filter.mp hx).2
  have hc : listedSeparatedCap D (threeHighGreedySeparated D R) = true := by
    apply greedySeparatedSet_cap
    simp [listedSeparatedCap]
  have hc' : ∀ S ∈ F, (threeHighGreedySeparated D R ∩ S).card ≤ 1 := by
    intro S hS
    exact of_decide_eq_true (List.all_eq_true.mp hc S (hD S hS))
  have hb := card_le_covering_family_of_inter_card_le_one
    (threeHighGreedySeparated D R) F (by simpa only [hf.2.2.2] using hs) hc'
  apply decide_eq_true_iff.mpr
  simpa only [hf.2.1] using hb

end Erdos85
#print axioms Erdos85.threeHighSeparatedGate_of_resolution
