import Proofs.Erdos85OrderFortyNineThreeHighTripleTerminalCertificate
import Proofs.Erdos85EncodedC4Pruning

namespace Erdos85

theorem threeHighEligibleTriples_of_subgraph
    (A B : Fin 24 → Fin 24 → Bool) (hsub : EncodedSubgraph A B)
    (R S : Finset (Fin 24)) (hS : S ∈ threeHighEligibleTriples B R) :
    S ∈ threeHighEligibleTriples A R := by
  obtain ⟨hSR,hcard,hpair⟩ := (mem_threeHighEligibleTriples B R S).mp hS
  apply (mem_threeHighEligibleTriples A R S).mpr
  refine ⟨hSR,hcard,?_⟩
  intro x hx y hy hxy z hz
  exact hpair x hx y hy hxy z ⟨hsub _ _ hz.1,hsub _ _ hz.2⟩

theorem threeHighResolutionDomain_of_subgraph
    (A B : Fin 24 → Fin 24 → Bool) (hsub : EncodedSubgraph A B)
    (R : Finset (Fin 24)) (F : Finset (Finset (Fin 24)))
    (hF : F ∈ threeHighResolutionDomain B R) :
    F ∈ threeHighResolutionDomain A R := by
  obtain ⟨hsubF,hcard,hdis,hcover⟩ := (mem_threeHighResolutionDomain B R F).mp hF
  apply (mem_threeHighResolutionDomain A R F).mpr
  exact ⟨fun S hS => threeHighEligibleTriples_of_subgraph A B hsub R S (hsubF hS),
    hcard,hdis,hcover⟩

theorem encodedCrossIndependent_of_subgraph
    (A B : Fin 24 → Fin 24 → Bool) (hsub : EncodedSubgraph A B)
    (S T : Finset (Fin 24)) (h : encodedCrossIndependent B S T = true) :
    encodedCrossIndependent A S T = true := by
  unfold encodedCrossIndependent at h ⊢
  simp only [decide_eq_true_eq] at h ⊢
  intro i hi j hj
  cases ha : A i j
  · rfl
  · have hb := hsub i j ha
    rw [h i hi j hj] at hb
    cases hb

theorem encodedFamilyCompatibility_of_subgraph
    (A B : Fin 24 → Fin 24 → Bool) (hsub : EncodedSubgraph A B)
    (F K : Finset (Finset (Fin 24))) (h : encodedFamilyCompatibility B F K = true) :
    encodedFamilyCompatibility A F K = true := by
  unfold encodedFamilyCompatibility at h ⊢
  simp only [decide_eq_true_eq] at h ⊢
  intro S hS
  obtain ⟨T,hT,hST⟩ := h S hS
  exact ⟨T,hT,encodedCrossIndependent_of_subgraph A B hsub S T hST⟩

/-- Keep all three families together when deleting edges. -/
theorem ThreeHighJointWitness.of_subgraph
    (A B : Fin 24 → Fin 24 → Bool) (hsub : EncodedSubgraph A B)
    (hB : ThreeHighJointWitness B) : ThreeHighJointWitness A := by
  obtain ⟨F,hF,hblock,hcompat,hcap⟩ := hB
  refine ⟨F,?_,hblock,?_,hcap⟩
  · intro k
    exact threeHighResolutionDomain_of_subgraph A B hsub _ _ (hF k)
  · intro i j
    exact encodedFamilyCompatibility_of_subgraph A B hsub _ _ (hcompat i j)

/-- A sound terminal rejection on a partial graph rules out joint witnesses in all extensions. -/
theorem threeHighTerminal_reject_extension
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (hs : ThreeHighTerminalSound accept)
    (A B : Fin 24 → Fin 24 → Bool) (hsub : EncodedSubgraph A B)
    (ha : accept A = false) : ¬ ThreeHighJointWitness B := by
  intro hB
  have h := hs A (hB.of_subgraph A B hsub)
  rw [ha] at h
  cases h

end Erdos85
#print axioms Erdos85.threeHighEligibleTriples_of_subgraph
#print axioms Erdos85.threeHighResolutionDomain_of_subgraph
#print axioms Erdos85.encodedCrossIndependent_of_subgraph
#print axioms Erdos85.encodedFamilyCompatibility_of_subgraph
#print axioms Erdos85.ThreeHighJointWitness.of_subgraph
#print axioms Erdos85.threeHighTerminal_reject_extension
