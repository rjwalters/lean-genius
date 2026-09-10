import Proofs.Erdos85ThreeHighPivotResolution

namespace Erdos85

/-- Test one triple directly, without constructing the eligible-family Finset. -/
def threeHighTripleEligible (B : Fin 24 → Fin 24 → Bool)
    (R S : Finset (Fin 24)) : Bool :=
  decide (S ⊆ R ∧ S.card = 3 ∧
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ c, ¬ (B a c = true ∧ B b c = true))

def threeHighDirectTripleList (B : Fin 24 → Fin 24 → Bool) (R : Finset (Fin 24)) :
    List (Finset (Fin 24)) :=
  threeHighTripleList.filter (threeHighTripleEligible B R)

theorem threeHighTripleEligible_eq (B : Fin 24 → Fin 24 → Bool)
    (R S : Finset (Fin 24)) :
    threeHighTripleEligible B R S = decide (S ∈ threeHighEligibleTriples B R) := by
  apply Bool.decide_congr
  exact (mem_threeHighEligibleTriples B R S).symm

theorem threeHighDirectTripleList_eq (B : Fin 24 → Fin 24 → Bool)
    (R : Finset (Fin 24)) :
    threeHighDirectTripleList B R = threeHighEligibleTripleList B R := by
  unfold threeHighDirectTripleList threeHighEligibleTripleList
  congr 1
  funext S
  exact threeHighTripleEligible_eq B R S

def threeHighDirectResolutionSearch (B : Fin 24 → Fin 24 → Bool)
    (R : Finset (Fin 24)) : Bool :=
  finitePivotCoverSearch (threeHighDirectTripleList B R) 6 R

theorem threeHighDirectResolutionSearch_eq (B : Fin 24 → Fin 24 → Bool)
    (R : Finset (Fin 24)) :
    threeHighDirectResolutionSearch B R = threeHighPivotResolutionSearch B R := by
  unfold threeHighDirectResolutionSearch threeHighPivotResolutionSearch
  rw [threeHighDirectTripleList_eq]

theorem threeHighDirectResolutionSearch_of_mem (B : Fin 24 → Fin 24 → Bool)
    (R : Finset (Fin 24)) (F : Finset (Finset (Fin 24)))
    (hF : F ∈ threeHighResolutionDomain B R) : threeHighDirectResolutionSearch B R = true := by
  rw [threeHighDirectResolutionSearch_eq]
  exact threeHighPivotResolutionSearch_of_mem B R F hF

end Erdos85
#print axioms Erdos85.threeHighTripleEligible_eq
#print axioms Erdos85.threeHighDirectTripleList_eq
#print axioms Erdos85.threeHighDirectResolutionSearch_eq
#print axioms Erdos85.threeHighDirectResolutionSearch_of_mem
