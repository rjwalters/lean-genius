import Mathlib

namespace Erdos85

/-- Triples that cannot create a C4 through their singleton vertex. -/
def threeHighEligibleTriples (B : Fin 24 → Fin 24 → Bool) (R : Finset (Fin 24)) :
    Finset (Finset (Fin 24)) :=
  (R.powersetCard 3).filter fun S =>
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ c, ¬ (B a c = true ∧ B b c = true)

/-- Six eligible, disjoint triples covering exactly the prescribed residual labels. -/
def threeHighResolutionDomain (B : Fin 24 → Fin 24 → Bool) (R : Finset (Fin 24)) :
    Finset (Finset (Finset (Fin 24))) :=
  ((threeHighEligibleTriples B R).powersetCard 6).filter fun F =>
    (∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T) ∧ F.biUnion id = R

theorem mem_threeHighEligibleTriples (B : Fin 24 → Fin 24 → Bool)
    (R S : Finset (Fin 24)) :
    S ∈ threeHighEligibleTriples B R ↔ S ⊆ R ∧ S.card = 3 ∧
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ c, ¬ (B a c = true ∧ B b c = true)) := by
  simp only [threeHighEligibleTriples, Finset.mem_filter, Finset.mem_powersetCard]
  tauto

theorem mem_threeHighResolutionDomain (B : Fin 24 → Fin 24 → Bool)
    (R : Finset (Fin 24)) (F : Finset (Finset (Fin 24))) :
    F ∈ threeHighResolutionDomain B R ↔
      F ⊆ threeHighEligibleTriples B R ∧ F.card = 6 ∧
      (∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T) ∧ F.biUnion id = R := by
  simp only [threeHighResolutionDomain, Finset.mem_filter, Finset.mem_powersetCard]
  tauto

end Erdos85
#print axioms Erdos85.mem_threeHighEligibleTriples
#print axioms Erdos85.mem_threeHighResolutionDomain
