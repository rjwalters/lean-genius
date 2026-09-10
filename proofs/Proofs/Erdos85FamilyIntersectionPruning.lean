import Proofs.Erdos85OrderFortyNineThreeHighTripleColorFamilyIntersection

namespace Erdos85

theorem encodedFamilyIntersectionCap_mono
    (F K F' K' : Finset (Finset (Fin 24))) (hF : F ⊆ F') (hK : K ⊆ K')
    (hcap : encodedFamilyIntersectionCap F' K' = true) :
    encodedFamilyIntersectionCap F K = true := by
  have h := of_decide_eq_true hcap
  apply decide_eq_true_iff.mpr
  intro S hS T hT
  exact h S (hF hS) T (hK hT)

theorem encodedFamilyIntersectionCap_reject_extensions
    (F K : Finset (Finset (Fin 24))) (hbad : encodedFamilyIntersectionCap F K = false) :
    ∀ F' K', F ⊆ F' → K ⊆ K' → encodedFamilyIntersectionCap F' K' = false := by
  intro F' K' hF hK
  cases hc : encodedFamilyIntersectionCap F' K'
  · rfl
  · have hp := encodedFamilyIntersectionCap_mono F K F' K' hF hK hc
    rw [hbad] at hp
    contradiction

end Erdos85
#print axioms Erdos85.encodedFamilyIntersectionCap_mono
#print axioms Erdos85.encodedFamilyIntersectionCap_reject_extensions
